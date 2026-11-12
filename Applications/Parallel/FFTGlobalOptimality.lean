import Applications.Parallel.FFTConstruction
import Applications.Parallel.FFTOptimality

/-! Pair-composed normalized FFTs attain both global fixed-register lower bounds. -/
namespace Applications.Parallel.FFTUnitary

open scoped Matrix

theorem normalizedProgram_gate_minimizer (s : Factor) :
    normalizedProgram s ∈ Optimization.minimizers (feasible s.size) Program.gateCount :=
  gate_minimizer_of_counts s (normalizedProgram s)
    (normalizedProgram_correct s) (normalizedProgram_gateCount s)

theorem normalizedProgram_round_minimizer (s : Factor) :
    normalizedProgram s ∈ Optimization.minimizers (feasible s.size) Program.roundCount :=
  round_minimizer_of_counts s (normalizedProgram s)
    (normalizedProgram_correct s) (normalizedProgram_roundCount s)

/-- The in-place realization computes the existing FFT, with normalization and the
reversed output shape made explicit. -/
theorem normalizedProgram_fft_decode (s : Factor) (x : s.Data ℂ)
    (k : Fin s.reverse.size) :
    (((normalizedProgram s).unitary : Matrix (Fin s.size) (Fin s.size) ℂ) *ᵥ s.decode x)
      (Fin.cast s.size_reverse k) =
      normalization s.size * s.reverse.decode (s.fft s.fourierRoot x) k := by
  rw [normalizedProgram_correct]
  exact (normalized_fft_decode s x k).symm

/-- The new machine realizes the measured prerequisite circuit's outputs exactly. -/
theorem normalizedProgram_compile_decode (s : Factor) (v : Nat → ℂ)
    (inputs : s.Data (Factor.Expr ℂ)) (k : Fin s.reverse.size) :
    normalization s.size * s.reverse.decode
      (s.reverse.map (Factor.Expr.eval v) (s.compile s.fourierRoot inputs).outputs) k =
    (((normalizedProgram s).unitary : Matrix (Fin s.size) (Fin s.size) ℂ) *ᵥ
      s.decode (s.map (Factor.Expr.eval v) inputs)) (Fin.cast s.size_reverse k) := by
  change normalization s.size * s.reverse.decode
    (s.reverse.map (Factor.Expr.eval v) (s.expressions s.fourierRoot inputs)) k = _
  rw [s.expressions_eval]
  exact (normalizedProgram_fft_decode s _ k).symm

theorem normalizedProgram_gateCount_eq_compile (s : Factor)
    (inputs : s.Data (Factor.Expr ℂ)) :
    (normalizedProgram s).gateCount = (s.compile s.fourierRoot inputs).butterflies.length := by
  rw [normalizedProgram_gateCount]
  exact (s.compile_counts s.fourierRoot inputs).1.symm

/-- Attainment is witnessed by the constructed program for every factor shape. -/
theorem normalizedProgram_attains (s : Factor) :
    Optimization.Attained (feasible s.size) Program.gateCount ∧
      Optimization.Attained (feasible s.size) Program.roundCount :=
  ⟨⟨normalizedProgram s, normalizedProgram_gate_minimizer s⟩,
    ⟨normalizedProgram s, normalizedProgram_round_minimizer s⟩⟩

end Applications.Parallel.FFTUnitary
