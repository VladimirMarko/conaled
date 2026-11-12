import Applications.Parallel.FFTNetwork
import Applications.Parallel.FFTNormalization

/-! An attaining normalized network for every pair-composed factor tree. -/
namespace Applications.Parallel.FFTUnitary
open scoped BigOperators Matrix

noncomputable def hadamardGate : Gate 2 := Gate.ofPair (Function.Embedding.refl _) hadamard
@[simp] theorem hadamardGate_coordinate (i : Fin 2) : hadamardGate.coordinate i = i :=
  Gate.ofPair_coordinate _ _ i
noncomputable def hadamardRound : Round 2 := ⟨[hadamardGate],by simp⟩
theorem hadamardRound_complete : hadamardRound.Complete := by
  intro i
  exact ⟨hadamardGate,by simp [hadamardRound],i,hadamardGate_coordinate i⟩

theorem hadamardRound_mulVec (x : Fin 2 → ℂ) :
    (hadamardRound.unitary : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x = fourierMatrix 2 *ᵥ x := by
  funext i
  have h := matching_mul_coordinate hadamardRound.gates hadamardRound.disjoint
    hadamardGate (by simp [hadamardRound]) i (fun a _ => x a) i
  simp only [hadamardGate_coordinate] at h
  change _ = ∑ b, hadamardMatrix i b * x b at h
  change ((hadamardRound.unitary : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) i =
    (hadamardMatrix *ᵥ x) i at h
  rw [hadamard_fourier] at h
  exact h

def columnFrame (s t : Factor) : Fin t.size × Fin s.size ≃ Fin (s.size*t.size) :=
  (Equiv.prodComm _ _).trans finProdFinEquiv

def outputPermutation (s t : Factor) : Equiv.Perm (Fin (s.size*t.size)) :=
  (((finCongr (Nat.mul_comm s.size t.size)).trans finProdFinEquiv.symm).trans
    (Equiv.prodComm _ _)).trans finProdFinEquiv

noncomputable def twiddlePhases (s t : Factor) (i : Fin (s.size*t.size)) : _root_.unitary ℂ :=
  let p : Fin s.size × Fin t.size := finProdFinEquiv.symm i
  phaseUnitary (s.size*t.size) (p.1.val*p.2.val)

noncomputable def normalizedProgram : (s : Factor) → Program s.size
  | .one => []
  | .two => [.round hadamardRound]
  | .comp s t =>
    (normalizedProgram s).copies (columnFrame s t) ++
    ((normalizedProgram t).copies finProdFinEquiv).absorb (twiddlePhases s t) ++
    [Step.permute (outputPermutation s t)]

@[simp] theorem normalizedProgram_gateCount (s : Factor) :
    (normalizedProgram s).gateCount = s.butterflies := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t hs ht =>
    change ((normalizedProgram s).copies (columnFrame s t) ++
      ((normalizedProgram t).copies finProdFinEquiv).absorb (twiddlePhases s t) ++
      [Step.permute (outputPermutation s t)]).gateCount = _
    rw [Program.gateCount_append,Program.gateCount_append,Program.absorb_gateCount,
      Program.copies_gateCount,Program.copies_gateCount,hs,ht]
    rfl

@[simp] theorem normalizedProgram_roundCount (s : Factor) :
    (normalizedProgram s).roundCount = s.logSize := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t hs ht =>
    change ((normalizedProgram s).copies (columnFrame s t) ++
      ((normalizedProgram t).copies finProdFinEquiv).absorb (twiddlePhases s t) ++
      [Step.permute (outputPermutation s t)]).roundCount = _
    rw [Program.roundCount_append,Program.roundCount_append,Program.absorb_roundCount,
      Program.copies_roundCount,Program.copies_roundCount,hs,ht]
    rfl

theorem normalizedProgram_complete (s : Factor) : (normalizedProgram s).Complete := by
  induction s with
  | one => simp [normalizedProgram,Program.Complete]
  | two =>
    intro step hs
    simp only [normalizedProgram,List.mem_singleton] at hs
    subst step
    exact hadamardRound_complete
  | comp s t hs ht =>
    apply Program.complete_append
    · exact Program.complete_append _ _ (Program.copies_complete _ _ hs)
        (Program.absorb_complete _ _ (Program.copies_complete _ _ ht))
    · intro step h
      change step ∈ [Step.permute (outputPermutation s t)] at h
      have eq := List.mem_singleton.mp h
      subst step
      trivial

/-- A zero-round child may be syntactically composite, but has exactly one
register, so its composition twiddles are the identity. -/
theorem twiddlePhases_singleton (s t : Factor) (ht : t.logSize = 0)
    (i : Fin (s.size*t.size)) : twiddlePhases s t i = 1 := by
  have size : t.size = 1 := by simpa [ht] using t.size_eq_pow
  have zero : ((finProdFinEquiv.symm i : Fin s.size × Fin t.size).2).val = 0 := by
    have h := (finProdFinEquiv.symm i : Fin s.size × Fin t.size).2.isLt
    omega
  apply Subtype.ext
  simp only [twiddlePhases,phaseUnitary_coe,zero,Nat.mul_zero,FFTScalar.phase_zero]
  rfl

theorem permute_mulVec {N : ℕ} (p : Equiv.Perm (Fin N)) (x : Fin N → ℂ) :
    ((Step.permute p).unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ x = x ∘ p := by
  funext i
  simp [Step.unitary,Matrix.mulVec,dotProduct,Matrix.submatrix_apply,Matrix.one_apply]

theorem program_append_mulVec {N : ℕ} (p q : Program N) (x : Fin N → ℂ) :
    ((p ++ q).unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ x =
      (q.unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ ((p.unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ x) := by
  rw [Program.unitary_append]
  exact (Matrix.mulVec_mulVec x _ _).symm

theorem single_permute_mulVec {N : ℕ} (p : Equiv.Perm (Fin N)) (x : Fin N → ℂ) :
    (Program.unitary [Step.permute p] : Matrix (Fin N) (Fin N) ℂ) *ᵥ x = x ∘ p := by
  simpa only [Program.unitary,one_mul] using permute_mulVec p x

set_option backward.dsimp.instances true in
theorem normalizedProgram_mulVec (s : Factor) (x : Fin s.size → ℂ) :
    ((normalizedProgram s).unitary : Matrix (Fin s.size) (Fin s.size) ℂ) *ᵥ x =
      fourierMatrix s.size *ᵥ x := by
  induction s with
  | one =>
    dsimp only [Factor.size] at x ⊢
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ x = fourierMatrix 1 *ᵥ x
    rw [Matrix.one_mulVec]
    funext i
    fin_cases i
    simp [fourierMatrix,Matrix.mulVec,dotProduct,FFTScalar.phase_zero]
  | two =>
    dsimp only [Factor.size] at x ⊢
    simpa only [normalizedProgram,Program.unitary,Step.unitary,one_mul] using hadamardRound_mulVec x
  | comp s t hs ht =>
    dsimp only [Factor.size] at x ⊢
    have first (b : Fin t.size) (c : Fin s.size) :
        ((((normalizedProgram s).copies (columnFrame s t)).unitary : Matrix (Fin (s.size*t.size)) (Fin (s.size*t.size)) ℂ) *ᵥ x) (finProdFinEquiv (c,b)) =
          (fourierMatrix s.size *ᵥ fun a => x (finProdFinEquiv (a,b))) c := by
      have h := Program.copies_mulVec (columnFrame s t) (normalizedProgram s)
        (normalizedProgram_complete s) x b c
      rw [hs] at h
      simpa [columnFrame] using h
    have phaseEmpty : ((normalizedProgram t).copies (finProdFinEquiv (m := s.size) (n := t.size))).roundCount = 0 →
        ∀ i, twiddlePhases s t i = 1 := by
      intro h i
      exact twiddlePhases_singleton s t (by simpa using h) i
    funext k
    let output : Fin t.size × Fin s.size ≃ Fin (s.size*t.size) :=
      finProdFinEquiv.trans (finCongr (Nat.mul_comm t.size s.size))
    obtain ⟨⟨d,c⟩,rfl⟩ := output.surjective k
    change (((Program.unitary ((normalizedProgram s).copies (columnFrame s t) ++
      ((normalizedProgram t).copies finProdFinEquiv).absorb (twiddlePhases s t) ++
      [Step.permute (outputPermutation s t)])) : Matrix (Fin (s.size*t.size)) (Fin (s.size*t.size)) ℂ) *ᵥ x) (output (d,c)) = _
    rw [program_append_mulVec,program_append_mulVec,single_permute_mulVec]
    simp only [Function.comp_apply]
    have outIndex : outputPermutation s t (output (d,c)) = finProdFinEquiv (c,d) := by
      simp [outputPermutation,output]
    rw [outIndex]
    rw [Program.absorb_mulVec _ _ (Program.copies_complete _ _ (normalizedProgram_complete t)) phaseEmpty]
    rw [Program.copies_mulVec _ _ (normalizedProgram_complete t),ht]
    simp_rw [first]
    simp only [twiddlePhases,Equiv.symm_apply_apply,phaseUnitary_coe]
    change _ = (fourierMatrix (s.size*t.size) *ᵥ x)
      (Fin.cast (Nat.mul_comm t.size s.size) (finProdFinEquiv (d,c)))
    rw [fourierMatrix_comp_mulVec]
    rfl

/-- Exact normalized Fourier semantics, including the final register permutation. -/
theorem normalizedProgram_correct (s : Factor) :
    ((normalizedProgram s).unitary : Matrix (Fin s.size) (Fin s.size) ℂ) = fourierMatrix s.size := by
  apply Matrix.mulVec_injective
  funext x
  exact normalizedProgram_mulVec s x

end Applications.Parallel.FFTUnitary
