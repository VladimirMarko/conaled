import Applications.Probability.BoundedUniformLaw
import Applications.Probability.UniformThreeLaw

/-!
# Checked bounded sampling

Width is the least positive binary width covering the bound. Bound 1 therefore
has constant output but random work: bit 1 rejects and bit 0 accepts. Work counts
bit-reading transitions, without charging for arithmetic on the accumulator.
-/
namespace Examples.BoundedUniform
open Applications.Probability
open Applications.Probability.BoundedUniform
open MeasureTheory
open scoped ENNReal

example : width 1=1 ∧ width 2=1 ∧ width 3=2 ∧ width 5=3 := by decide
example : Progress.search (step 1 (fun _ => false)) 1 (start 1 0)=some ((0,1),1) := by decide
example : Progress.search (step 1 (fun i => decide (i=0))) 1 (start 1 0)=none := by decide
example : Progress.search (step 1 (fun i => decide (i=0))) 2 (start 1 0)=some ((0,2),2) := by decide
example : Progress.search (step 2 (fun _ => true)) 1 (start 2 7)=some ((1,8),1) := by decide

/-- At cursor 2, blocks 101, 110, 111 reject, then 100 returns 4. -/
def threeRejections : CoinPaths.Tape := fun i => decide (i=2 ∨ i=4 ∨ i=5 ∨ i=6 ∨
  i=8 ∨ i=9 ∨ i=10 ∨ i=11)

example : Progress.search (step 5 threeRejections) 11 (start 5 2)=none := by decide
example : Progress.search (step 5 threeRejections) 12 (start 5 2)=some ((4,14),12) := by decide
example : Progress.search (step 5 (fun _ => false)) 2 (start 5 0)=none := by decide
example : Progress.search (step 5 (fun _ => false)) 3 (start 5 0)=some ((0,3),3) := by decide

example : rejection 1=(2⁻¹ : ℝ≥0∞) := by norm_num [rejection,width,Nat.clog,← ENNReal.inv_pow,div_eq_mul_inv]
example : rejection 2=0 := rejection_zero 2 (by decide)
example : rejection 5=(3/8 : ℝ≥0∞) := by norm_num [rejection,width,Nat.clog,← ENNReal.inv_pow,div_eq_mul_inv]
example (a : Fin 5) : CoinPaths.law (returns 5 2 a)=(5⁻¹ : ℝ≥0∞) := returns_mass 5 2 a
example : CoinPaths.law {ω | Progress.search (step 5 ω) 11 (start 5 2)=none}=
    (3/8 : ℝ≥0∞)^3 := by
  rw [search_timeout_mass]
  norm_num [rejection,width,Nat.clog,← ENNReal.inv_pow,div_eq_mul_inv]

/-- One complete block gives mass 1/8 to each output, whereas uncapped sampling
above gives 1/5. A partial block cannot yet return. -/
example (a : Fin 5) : CoinPaths.law {ω |
    Progress.search (step 5 ω) 3 (start 5 0)=some ((a,3),3)}=(8⁻¹ : ℝ≥0∞) := by
  have hw : width 5=3 := by decide
  have he : {ω | Progress.search (step 5 ω) 3 (start 5 0)=some ((a,3),3)}=
      {ω | Accept 5 ω 0 0 a} := by
    ext ω
    constructor
    · intro h
      exact (evaluates_iff 5 ω 0 0 a).mp (by simpa [hw] using Progress.search_sound h)
    · intro h
      exact Progress.search_complete (by simpa [hw] using evaluates_of_accept h) (by decide)
  rw [he,accept_mass]
  norm_num [hw,← ENNReal.inv_pow]

example : ∀ᵐ ω ∂CoinPaths.law, Progress.Terminates (step 5 ω) (start 5 2) :=
  ae_terminates 5 2 (by decide)
example (B : Set CoinPaths.Tape) (hB : MeasurableSet B) :
    CoinPaths.law (selectedSuffix 5 2 (fun r a => r=3 ∧ a=4) B)=
      CoinPaths.law (selected 5 2 (fun r a => r=3 ∧ a=4))*CoinPaths.law B :=
  random_cursor_fresh 5 2 _ B hB

/-- The old three-outcome sampler and the bounded sampler recognize the same
accepted prefixes, for every tape, initial cursor, retry count and output. -/
theorem accept_three_iff (ω : CoinPaths.Tape) (s r : ℕ) (a : Fin 3) :
    Accept 3 ω s r a ↔ UniformThree.Accept ω s r a := by
  have hw : width 3=2 := by decide
  induction r generalizing s with
  | zero =>
    rw [Accept,hw,UniformThree.accept_zero]
    fin_cases a <;> cases h0 : ω s <;> cases h1 : ω (s+1) <;>
      simp [BinaryBlock.read_succ,BinaryBlock.read_zero,UniformThree.firstBit,
        UniformThree.secondBit,h0,h1]
  | succ r ih =>
    simp only [Accept,hw,UniformThree.accept_succ]
    have hi := ih (s+2)
    simp only [hi]
    cases h0 : ω s <;> cases h1 : ω (s+1) <;>
      simp [BinaryBlock.read_succ,BinaryBlock.read_zero,h0,h1]

/-- Recovery includes the returned cursor and the exact bit-reading work,
not just the marginal output distribution. -/
theorem evaluates_three_iff (ω : CoinPaths.Tape) (s t k : ℕ) (a : Fin 3) :
    Progress.Evaluates (step 3 ω) (start 3 s) (a,t) k ↔
      Progress.Evaluates (UniformThree.step ω) (s,none) (a,t) k := by
  have hw : width 3=2 := by decide
  constructor
  · intro h
    obtain ⟨r,hr,ht,hk⟩ := accept_of_evaluates h
    rw [hw] at ht hk
    rw [ht,hk]
    exact UniformThree.evaluates_of_accept ((accept_three_iff _ _ _ _).mp hr)
  · intro h
    obtain ⟨r,hr,ht,hk⟩ := UniformThree.accept_of_evaluates h
    rw [ht,hk]
    simpa [hw] using evaluates_of_accept ((accept_three_iff _ _ _ _).mpr hr)

/-- Every finite fuel observation also agrees with the existing machine. -/
theorem search_three_eq (ω : CoinPaths.Tape) (s fuel : ℕ) :
    Progress.search (step 3 ω) fuel (start 3 s)=
      Progress.search (UniformThree.step ω) fuel (s,none) := by
  cases hb : Progress.search (step 3 ω) fuel (start 3 s) with
  | some p =>
    rcases p with ⟨⟨a,t⟩,k⟩
    exact (Progress.search_complete
      ((evaluates_three_iff ω s t k a).mp (Progress.search_sound hb))
      (ProbabilityProgress.search_cost_le hb)).symm
  | none =>
    cases hu : Progress.search (UniformThree.step ω) fuel (s,none) with
    | none => rfl
    | some p =>
      rcases p with ⟨⟨a,t⟩,k⟩
      have he := Progress.search_complete
        ((evaluates_three_iff ω s t k a).mpr (Progress.search_sound hu))
        (ProbabilityProgress.search_cost_le hu)
      rw [hb] at he
      contradiction

end Examples.BoundedUniform
