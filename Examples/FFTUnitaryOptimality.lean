import Applications.Parallel.FFTGlobalOptimality

/-! Global optimality clients include differing associations and nested singleton factors. -/
namespace Examples.FFTUnitaryOptimality

open Applications.Parallel Applications.Parallel.FFTUnitary

example : normalizedProgram Factor.one ∈
    Optimization.minimizers (feasible 1) Program.gateCount :=
  normalizedProgram_gate_minimizer .one

example : normalizedProgram Factor.two ∈
    Optimization.minimizers (feasible 2) Program.roundCount :=
  normalizedProgram_round_minimizer .two

example : (normalizedProgram (Factor.rightPow 4)).gateCount = 32 ∧
    (normalizedProgram (Factor.rightPow 4)).roundCount = 4 := by
  rw [normalizedProgram_gateCount, normalizedProgram_roundCount]
  decide

example : normalizedProgram (Factor.rightPow 4) ∈
    Optimization.minimizers (feasible (Factor.rightPow 4).size) Program.gateCount ∧
    normalizedProgram (Factor.rightPow 4) ∈
    Optimization.minimizers (feasible (Factor.rightPow 4).size) Program.roundCount :=
  ⟨normalizedProgram_gate_minimizer _, normalizedProgram_round_minimizer _⟩

example : normalizedProgram (Factor.leftPow 4) ∈
    Optimization.minimizers (feasible (Factor.leftPow 4).size) Program.gateCount ∧
    normalizedProgram (Factor.leftPow 4) ∈
    Optimization.minimizers (feasible (Factor.leftPow 4).size) Program.roundCount :=
  ⟨normalizedProgram_gate_minimizer _, normalizedProgram_round_minimizer _⟩

example : normalizedProgram (Factor.bush 2) ∈
    Optimization.minimizers (feasible (Factor.bush 2).size) Program.gateCount ∧
    normalizedProgram (Factor.bush 2) ∈
    Optimization.minimizers (feasible (Factor.bush 2).size) Program.roundCount :=
  ⟨normalizedProgram_gate_minimizer _, normalizedProgram_round_minimizer _⟩

example : (normalizedProgram (.comp (.comp .one .one) (.comp .one .one))).gateCount = 0 ∧
    (normalizedProgram (.comp (.comp .one .one) (.comp .one .one))).roundCount = 0 := by
  rw [normalizedProgram_gateCount, normalizedProgram_roundCount]
  decide

example : normalizedProgram (.comp (.comp .one .one) (Factor.rightPow 4)) ∈
    Optimization.minimizers
      (feasible (Factor.comp (.comp .one .one) (Factor.rightPow 4)).size) Program.gateCount :=
  normalizedProgram_gate_minimizer _

end Examples.FFTUnitaryOptimality
