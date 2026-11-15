import Applications.QuantumSemantics.Core
import Applications.Uncomputation.Coordinates

/-! Reuse the existing coherent permutation coordinates as admitted quantum gates. -/

namespace QuantumSemantics

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Existing reversible basis programs realize unitary density transformations. -/
noncomputable def permutationGate (e : n ≃ n) : Gate n where
  matrix := Uncomputation.coordinates e
  adjoint_mul := Uncomputation.coordinates_unitary e
  mul_adjoint := by
    have h := Uncomputation.coordinates_unitary e.symm
    simpa only [Uncomputation.coordinates_adjoint, Matrix.conjTranspose_conjTranspose] using h

/-- The old coordinate composition law preserves the new density denotation. -/
theorem permutation_composition (e f : n ≃ n) (ρ : Operator n) :
    conjugate (permutationGate (e.trans f)).matrix ρ =
      conjugate (permutationGate f).matrix (conjugate (permutationGate e).matrix ρ) := by
  simp [permutationGate, Uncomputation.coordinates_comp, conjugate,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end QuantumSemantics
