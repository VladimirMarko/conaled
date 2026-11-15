import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Applications.Parallel.FFTUnitary
import Mathlib.Analysis.Complex.Norm

/-! Matrix-entropy accounting for the fixed-register unitary FFT model. -/

namespace Applications.Parallel.FFTUnitary

noncomputable def entropyTerm (x : ℝ) : ℝ := Real.negMulLog x / Real.log 2

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by
  simp [entropyTerm]

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by
  simp [entropyTerm]

/-- Splitting mass into two coordinates adds between zero and one bit per unit mass.
The total mass need not be at most one. -/
theorem entropyTerm_pair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    entropyTerm (a + b) ≤ entropyTerm a + entropyTerm b ∧
      entropyTerm a + entropyTerm b ≤ entropyTerm (a + b) + (a + b) := by
  by_cases hz : a + b = 0
  · have hza : a = 0 := by linarith
    have hzb : b = 0 := by linarith
    simp [hza, hzb]
  have hr : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  let p := a / (a + b)
  have hp0 : 0 ≤ p := div_nonneg ha hr.le
  have hp1 : p ≤ 1 := (div_le_one hr).2 (by linarith)
  have hpa : (a + b) * p = a := by dsimp [p]; field_simp
  have hpb : (a + b) * (1 - p) = b := by rw [mul_sub, mul_one, hpa]; ring
  have he : Real.negMulLog a + Real.negMulLog b =
      Real.negMulLog (a + b) + (a + b) * Real.binEntropy p := by
    have ea := Real.negMulLog_mul (a + b) p
    have eb := Real.negMulLog_mul (a + b) (1 - p)
    rw [hpa] at ea
    rw [hpb] at eb
    rw [ea, eb, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    ring
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := Real.binEntropy_nonneg hp0 hp1
  have hu : Real.binEntropy p ≤ Real.log 2 := Real.binEntropy_le_log_two
  constructor
  · unfold entropyTerm
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hl).2
    rw [he]
    exact le_add_of_nonneg_right (mul_nonneg hr.le hn)
  · change (Real.negMulLog a / Real.log 2 + Real.negMulLog b / Real.log 2) ≤
      Real.negMulLog (a + b) / Real.log 2 + (a + b)
    rw [← add_div, he, add_div]
    exact add_le_add_right ((div_le_iff₀ hl).2 (mul_le_mul_of_nonneg_left hu hr.le)) _

/-- Two splittings of the same nonnegative mass differ by at most that mass. -/
theorem entropyTerm_pair_change {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b = c + d) :
    |(entropyTerm c + entropyTerm d) - (entropyTerm a + entropyTerm b)| ≤ a + b := by
  obtain ⟨hab₁, hab₂⟩ := entropyTerm_pair ha hb
  obtain ⟨hcd₁, hcd₂⟩ := entropyTerm_pair hc hd
  rw [← h] at hcd₁ hcd₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

section MatrixEntropy

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def matrixEntropy (M : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, entropyTerm (Complex.normSq (M i j))

@[simp] theorem matrixEntropy_one [DecidableEq ι] :
    matrixEntropy (1 : Matrix ι ι ℂ) = 0 := by
  simp [matrixEntropy, Matrix.one_apply, apply_ite]

theorem matrixEntropy_reindex {τ : Type*} [Fintype τ]
    (M : Matrix ι κ ℂ) (e : τ ≃ ι) :
    matrixEntropy (M.submatrix e id) = matrixEntropy M := by
  unfold matrixEntropy
  exact Equiv.sum_comp e (fun i => ∑ j, entropyTerm (Complex.normSq (M i j)))

theorem unitary_row_mass [DecidableEq ι] (M : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, Complex.normSq (M i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => (A i i).re)
    (Matrix.mem_unitaryGroup_iff.mp M.property)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply] using h

/-- A unitary block preserves the sum of squared coordinate magnitudes. -/
theorem unitary_mass [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ i, Complex.normSq (((U : Matrix ι ι ℂ) *ᵥ v) i) =
      ∑ i, Complex.normSq (v i) := by
  have he : star ((U : Matrix ι ι ℂ) *ᵥ v) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ v) =
      star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp U.property,
      Matrix.vecMul_one]
  have hr := congrArg Complex.re he
  simpa [dotProduct, Complex.mul_re, Complex.normSq_apply] using hr

/-- The two changed rows contribute at most two bits when their old masses are one. -/
theorem two_rows_entropy_change (a b c d : κ → ℂ)
    (ha : ∑ j, Complex.normSq (a j) = 1)
    (hb : ∑ j, Complex.normSq (b j) = 1)
    (hm : ∀ j, Complex.normSq (a j) + Complex.normSq (b j) =
      Complex.normSq (c j) + Complex.normSq (d j)) :
    |(∑ j, (entropyTerm (Complex.normSq (c j)) + entropyTerm (Complex.normSq (d j)))) -
      (∑ j, (entropyTerm (Complex.normSq (a j)) + entropyTerm (Complex.normSq (b j))))| ≤ 2 := by
  have hj (j : κ) := entropyTerm_pair_change
    (Complex.normSq_nonneg (a j)) (Complex.normSq_nonneg (b j))
    (Complex.normSq_nonneg (c j)) (Complex.normSq_nonneg (d j)) (hm j)
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (abs_le.mp (hj j)).2)
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (abs_le.mp (hj j)).1)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ha, hb] at hu hl ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Applying a block to the first two rows leaves every other row unchanged. -/
noncomputable def blockAct {τ : Type*} (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (M : Matrix (Fin 2 ⊕ τ) κ ℂ) : Matrix (Fin 2 ⊕ τ) κ ℂ :=
  Sum.elim (fun i j => ∑ t, U i t * M (.inl t) j) (fun i => M (.inr i))

theorem blockAct_entropy {τ : Type*} [Fintype τ]
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (M : Matrix (Fin 2 ⊕ τ) κ ℂ)
    (h0 : ∑ j, Complex.normSq (M (.inl 0) j) = 1)
    (h1 : ∑ j, Complex.normSq (M (.inl 1) j) = 1) :
    |matrixEntropy (blockAct U M) - matrixEntropy M| ≤ 2 := by
  have hm (j : κ) := unitary_mass U (fun t => M (.inl t) j)
  simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct] at hm
  have h := two_rows_entropy_change (M (.inl 0)) (M (.inl 1))
    (blockAct U M (.inl 0)) (blockAct U M (.inl 1)) h0 h1
    (fun j => by simpa [blockAct, Fin.sum_univ_two] using (hm j).symm)
  simp only [matrixEntropy, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [blockAct, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib] at h ⊢
  convert h using 1; congr 1; ring

omit [Fintype κ] in
theorem gate_mul_reindex {N : ℕ} (g : Gate N) (M : Matrix (Fin N) κ ℂ) :
    (g.matrix * M).submatrix g.frame.symm id =
      blockAct g.block (M.submatrix g.frame.symm id) := by
  ext i j
  change (g.matrix * M) (g.frame.symm i) j = _
  rw [Matrix.mul_apply, ← g.frame.symm.sum_comp
    (fun k => g.matrix (g.frame.symm i) k * M k j)]
  cases i <;> simp [Gate.matrix, Matrix.submatrix, Matrix.fromBlocks,
    Fintype.sum_sum_type, blockAct, Matrix.one_apply]

omit [Fintype κ] in
theorem gate_mul_coordinate {N : ℕ} (g : Gate N) (M : Matrix (Fin N) κ ℂ)
    (i : Fin 2) (j : κ) :
    (g.matrix * M) (g.coordinate i) j = ∑ t, g.block i t * M (g.coordinate t) j := by
  exact congrArg (fun A => A (.inl i) j) (gate_mul_reindex g M)

omit [Fintype κ] in
theorem gate_mul_outside {N : ℕ} (g : Gate N) (M : Matrix (Fin N) κ ℂ)
    (i : Fin N) (h : ∀ t, i ≠ g.coordinate t) (j : κ) :
    (g.matrix * M) i j = M i j := by
  have he := congrArg (fun A => A (g.frame i) j) (gate_mul_reindex g M)
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id_eq] at he
  cases hf : g.frame i with
  | inl t =>
    have hi : i = g.coordinate t := by
      apply g.frame.injective
      simpa [Gate.coordinate] using hf
    exact False.elim (h t hi)
  | inr t =>
    rw [hf] at he
    have hh := congrArg g.frame.symm hf
    simp only [Equiv.symm_apply_apply] at hh
    simpa [blockAct, ← hh] using he

/-- One admitted gate changes matrix entropy by at most two bits. -/
theorem gate_entropy_change {N : ℕ} (g : Gate N)
    (M : Matrix.unitaryGroup (Fin N) ℂ) :
    |matrixEntropy (g.matrix * (M : Matrix (Fin N) (Fin N) ℂ)) -
      matrixEntropy (M : Matrix (Fin N) (Fin N) ℂ)| ≤ 2 := by
  rw [← matrixEntropy_reindex _ g.frame.symm, gate_mul_reindex,
    ← matrixEntropy_reindex (M : Matrix (Fin N) (Fin N) ℂ) g.frame.symm]
  apply blockAct_entropy
  · exact unitary_row_mass M (g.coordinate 0)
  · exact unitary_row_mass M (g.coordinate 1)

theorem gates_entropy_le {N : ℕ} (gs : List (Gate N))
    (M : Matrix.unitaryGroup (Fin N) ℂ) :
    matrixEntropy ((Round.gatesUnitary gs * M : Matrix.unitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) ≤
      matrixEntropy (M : Matrix (Fin N) (Fin N) ℂ) + 2 * gs.length := by
  induction gs generalizing M with
  | nil => simp [Round.gatesUnitary]
  | cons g gs ih =>
    have hc := (abs_le.mp (gate_entropy_change g M)).2
    have hi := ih (g.unitary * M)
    simp only [Round.gatesUnitary, mul_assoc, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    change matrixEntropy ((Round.gatesUnitary gs * (g.unitary * M) :
      Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) ≤ _
    change matrixEntropy ((g.unitary * M : Matrix.unitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) - matrixEntropy (M : Matrix (Fin N) (Fin N) ℂ) ≤ 2 at hc
    linarith

theorem step_entropy_le {N : ℕ} (s : Step N)
    (M : Matrix.unitaryGroup (Fin N) ℂ) :
    matrixEntropy ((s.unitary * M : Matrix.unitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) ≤
      matrixEntropy (M : Matrix (Fin N) (Fin N) ℂ) + 2 * s.gateCount := by
  cases s with
  | round r => exact gates_entropy_le r.gates M
  | permute p =>
    change matrixEntropy ((1 : Matrix (Fin N) (Fin N) ℂ).submatrix p (Equiv.refl _) *
      (M : Matrix (Fin N) (Fin N) ℂ)) ≤ _
    rw [Matrix.one_submatrix_mul]
    simp [Step.gateCount, matrixEntropy_reindex]

theorem program_entropy_le_aux {N : ℕ} (p : Program N)
    (M : Matrix.unitaryGroup (Fin N) ℂ) :
    matrixEntropy ((p.unitary * M : Matrix.unitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) ≤
      matrixEntropy (M : Matrix (Fin N) (Fin N) ℂ) + 2 * p.gateCount := by
  induction p generalizing M with
  | nil => simp [Program.unitary, Program.gateCount]
  | cons s ss ih =>
    have hc := step_entropy_le s M
    have hi := ih (s.unitary * M)
    simp only [Program.unitary, mul_assoc, Program.gateCount, List.map_cons,
      List.sum_cons, Nat.cast_add]
    change matrixEntropy ((Program.unitary ss * (s.unitary * M) :
      Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) ≤ _
    change _ ≤ _ + 2 * ((ss.map Step.gateCount).sum : ℝ) at hi
    linarith

/-- Every admitted program's final entropy is at most twice its counted gates. -/
theorem program_entropy_le {N : ℕ} (p : Program N) :
    matrixEntropy (p.unitary : Matrix (Fin N) (Fin N) ℂ) ≤ 2 * p.gateCount := by
  simpa using program_entropy_le_aux p 1

/-- Zero mass and concentrated mass satisfy the public splitting bound. -/
example : entropyTerm 0 ≤ entropyTerm 0 + entropyTerm 0 ∧
    entropyTerm 0 + entropyTerm 0 ≤ entropyTerm 0 + 0 := by
  simpa only [zero_add] using entropyTerm_pair (a := 0) (b := 0) le_rfl le_rfl

/-- A column-pair total may exceed one; the entropy interval still applies. -/
example : entropyTerm 2 ≤ entropyTerm 1 + entropyTerm 1 ∧
    entropyTerm 1 + entropyTerm 1 ≤ entropyTerm 2 + 2 := by
  convert entropyTerm_pair (a := 1) (b := 1) (by norm_num) (by norm_num) using 1 <;> norm_num

end MatrixEntropy

end Applications.Parallel.FFTUnitary
