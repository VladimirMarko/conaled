import Applications.Parallel.FFTConstruction

/-! Checked native layer construction, including singleton syntax and associations. -/
namespace Examples.FFTNetwork
open Applications.Parallel Applications.Parallel.FFTUnitary
open scoped Matrix

example : normalizedProgram .one = [] := rfl

example : ((normalizedProgram .two).unitary.val : Matrix (Fin 2) (Fin 2) ℂ) = hadamardMatrix := by
  rw [normalizedProgram_correct,hadamard_fourier]
  rfl

example : (normalizedProgram (.comp .two .two)).gateCount = 4 ∧
    (normalizedProgram (.comp .two .two)).roundCount = 2 ∧
    (normalizedProgram (.comp .two .two)).Complete := by
  exact ⟨normalizedProgram_gateCount _,normalizedProgram_roundCount _,normalizedProgram_complete _⟩

def singleton : Factor := .comp (.comp .one .one) (.comp .one (.comp .one .one))

example : (normalizedProgram singleton).gateCount = 0 ∧
    (normalizedProgram singleton).roundCount = 0 :=
  ⟨normalizedProgram_gateCount _,normalizedProgram_roundCount _⟩

example (s : Factor) :
    ((normalizedProgram (.comp singleton s)).unitary :
      Matrix (Fin (Factor.comp singleton s).size) (Fin (Factor.comp singleton s).size) ℂ) =
      fourierMatrix (Factor.comp singleton s).size := normalizedProgram_correct _

example (s : Factor) :
    (normalizedProgram (.comp s singleton)).roundCount = s.logSize := by
  rw [normalizedProgram_roundCount]
  rfl

example : (normalizedProgram (Factor.rightPow 4)).gateCount = 32 ∧
    (normalizedProgram (Factor.leftPow 4)).gateCount = 32 ∧
    (normalizedProgram (Factor.bush 2)).gateCount = 32 :=
  ⟨normalizedProgram_gateCount _,normalizedProgram_gateCount _,normalizedProgram_gateCount _⟩

example : (normalizedProgram (Factor.rightPow 4)).roundCount = 4 ∧
    (normalizedProgram (Factor.leftPow 4)).roundCount = 4 ∧
    (normalizedProgram (Factor.bush 2)).roundCount = 4 :=
  ⟨normalizedProgram_roundCount _,normalizedProgram_roundCount _,normalizedProgram_roundCount _⟩

example : ((normalizedProgram (Factor.rightPow 4)).unitary.val : Matrix (Fin 16) (Fin 16) ℂ) =
    ((normalizedProgram (Factor.bush 2)).unitary.val : Matrix (Fin 16) (Fin 16) ℂ) := by
  exact (normalizedProgram_correct (Factor.rightPow 4)).trans (normalizedProgram_correct (Factor.bush 2)).symm

/-- Each lifted layer remains complete, with two copies and no extra coordinates. -/
example : (hadamardRound.copies (finProdFinEquiv (m := 2) (n := 2))).gateCount = 2 ∧
    (hadamardRound.copies (finProdFinEquiv (m := 2) (n := 2))).Complete := by
  constructor
  · rw [Round.copies_gateCount]; rfl
  · exact Round.copies_complete _ _ hadamardRound_complete

/-- Absorbing arbitrary unit phases into a complete size-two layer retains its
single gate and changes its actual matrix action by precisely that diagonal. -/
example (d : Fin 2 → _root_.unitary ℂ) :
    (hadamardRound.absorb d).gateCount = 1 ∧
    (hadamardRound.absorb d).unitary = hadamardRound.unitary * diagonalUnitary d :=
  ⟨Round.absorb_gateCount _ _,Round.absorb_unitary _ _ hadamardRound_complete⟩

end Examples.FFTNetwork
