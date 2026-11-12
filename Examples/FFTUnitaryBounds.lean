import Applications.Parallel.FFTOptimality

/-! Checked lower bounds for arbitrary Fourier programs, with the size-one attainment. -/

namespace Examples.FFTUnitaryBounds

open Applications.Parallel Applications.Parallel.FFTUnitary

example : ([] : Program 1) ∈ Optimization.minimizers (feasible 1) Program.gateCount ∧
    ([] : Program 1) ∈ Optimization.minimizers (feasible 1) Program.roundCount :=
  empty_minimizers

example (p : Program 2) (hp : p ∈ feasible 2) :
    1 ≤ p.gateCount ∧ 1 ≤ p.roundCount :=
  ⟨factor_gate_lower_bound .two p hp, fourier_round_lower_bound .two p hp⟩

example (p : Program (Factor.rightPow 4).size) (hp : p ∈ feasible (Factor.rightPow 4).size) :
    32 ≤ p.gateCount ∧ 4 ≤ p.roundCount :=
  ⟨factor_gate_lower_bound (Factor.rightPow 4) p hp,
    fourier_round_lower_bound (Factor.rightPow 4) p hp⟩

example (p : Program (Factor.leftPow 4).size) (hp : p ∈ feasible (Factor.leftPow 4).size) :
    32 ≤ p.gateCount ∧ 4 ≤ p.roundCount :=
  ⟨factor_gate_lower_bound (Factor.leftPow 4) p hp,
    fourier_round_lower_bound (Factor.leftPow 4) p hp⟩

example (p : Program (Factor.bush 2).size) (hp : p ∈ feasible (Factor.bush 2).size) :
    32 ≤ p.gateCount ∧ 4 ≤ p.roundCount :=
  ⟨factor_gate_lower_bound (Factor.bush 2) p hp,
    fourier_round_lower_bound (Factor.bush 2) p hp⟩

example : matrixEntropy (fourierMatrix 2) = 2 := by
  have h := fourierMatrix_entropy Factor.two.size_pos
  rw [factor_log] at h
  norm_num [Factor.size, Factor.logSize] at h
  exact h

example : matrixEntropy (fourierMatrix 16) = 64 := by
  have h := fourierMatrix_entropy (Factor.rightPow 4).size_pos
  rw [factor_log] at h
  norm_num [Factor.rightPow, Factor.size, Factor.logSize] at h
  exact h

end Examples.FFTUnitaryBounds
