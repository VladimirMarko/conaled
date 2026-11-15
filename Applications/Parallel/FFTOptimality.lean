import Applications.Parallel.NormalizedFourier
import Applications.Optimization.Basic

/-! Global optimization contracts over all admitted fixed-register programs. -/

namespace Applications.Parallel.FFTUnitary

/-- All exact programs are candidates, regardless of their construction or gate values. -/
def feasible (N : ℕ) : Set (Program N) :=
  {p | (p.unitary : Matrix (Fin N) (Fin N) ℂ) = fourierMatrix N}

/-- Any realization attaining the butterfly count minimizes gates globally in this model. -/
theorem gate_minimizer_of_counts (s : Factor) (p : Program s.size)
    (hp : p ∈ feasible s.size) (hc : p.gateCount = s.butterflies) :
    p ∈ Optimization.minimizers (feasible s.size) Program.gateCount := by
  refine ⟨hp, ?_⟩
  intro q hq
  change p.gateCount ≤ q.gateCount
  rw [hc]
  exact factor_gate_lower_bound s q hq

/-- Round minimization uses input dependence, independently of entropy accounting. -/
theorem round_minimizer_of_counts (s : Factor) (p : Program s.size)
    (hp : p ∈ feasible s.size) (hc : p.roundCount = s.logSize) :
    p ∈ Optimization.minimizers (feasible s.size) Program.roundCount := by
  refine ⟨hp, ?_⟩
  intro q hq
  change p.roundCount ≤ q.roundCount
  rw [hc]
  exact fourier_round_lower_bound s q hq

@[simp] theorem fourierMatrix_one : fourierMatrix 1 = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [fourierMatrix, FFTScalar.phase]

/-- At size one, the empty program attains both global minima. -/
theorem empty_minimizers :
    ([] : Program 1) ∈ Optimization.minimizers (feasible 1) Program.gateCount ∧
    ([] : Program 1) ∈ Optimization.minimizers (feasible 1) Program.roundCount := by
  have hp : ([] : Program 1) ∈ feasible 1 := by
    simp [feasible, Program.unitary]
  exact ⟨gate_minimizer_of_counts .one [] hp rfl,
    round_minimizer_of_counts .one [] hp rfl⟩

end Applications.Parallel.FFTUnitary
