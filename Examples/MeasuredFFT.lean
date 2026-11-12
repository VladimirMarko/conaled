import Examples.FFTScalarCosts

/-! Checked clients of the structural and scalar Fourier circuit interpretations. -/
namespace Examples.MeasuredFFT
open Applications.Parallel
open Applications.Parallel.Factor
open Applications.Parallel.FFTScalar

/-- The singleton and pair conventions distinguish structural twiddles from
truncated natural subtraction. -/
theorem small_counts :
    Factor.one.butterflies = 0 ∧ Factor.one.twiddles = 0 ∧
    Factor.two.butterflies = 1 ∧ Factor.two.twiddles = 0 := by decide +kernel

theorem truncated_formula_fails_at_two :
    (1 * 2 ^ 1 / 2 - 2 ^ 1 + 1 : Nat) ≠ Factor.two.twiddles := by decide +kernel

theorem corrected_two_formula :
    Factor.two.twiddles = (Factor.two.logSize * Factor.two.size / 2 + 1) - Factor.two.size :=
  Factor.two.twiddles_closed

theorem sixteen_structural :
    (rightPow 4).butterflies = 32 ∧ (leftPow 4).butterflies = 32 ∧
    (bush 2).butterflies = 32 ∧ (rightPow 4).twiddles = 17 ∧
    (leftPow 4).twiddles = 17 ∧ (bush 2).twiddles = 17 := by decide +kernel

theorem bush_inventory {R : Type*} [CommSemiring R]
    (ω : R) (x : (bush 2).Data (Expr R)) :
    ((bush 2).compile ω x).butterflies.length = 32 ∧
      ((bush 2).compile ω x).twiddles.length = 17 := by
  simpa [butterflies, twiddles, bush, Factor.size] using (bush 2).compile_counts ω x

theorem scalar_singleton :
    (circuit false .one).work = 0 ∧ (circuit true .one).depth = 0 := by decide +kernel

theorem scalar_pair :
    (circuit false .two).work = 4 ∧ (circuit true .two).depth = 1 := by decide +kernel

set_option maxRecDepth 8192 in
/-- Equal structural counts do not determine scalar arithmetic costs. -/
theorem same_structure_different_cost :
    (rightPow 4).butterflies = (bush 2).butterflies ∧
    (rightPow 4).twiddles = (bush 2).twiddles ∧
    (circuit true (bush 2)).work < (circuit true (rightPow 4)).work := by
  have hc := counts_of_same_size (rightPow 4) (bush 2) (by decide)
  have ht : (circuit true (rightPow 4)).work = 176 := (Prod.mk.inj right_rewritten).1
  have hb : (circuit true (bush 2)).work = 168 := (Prod.mk.inj bush_rewritten).1
  refine ⟨hc.1, hc.2, ?_⟩
  exact lt_of_eq_of_lt hb (lt_of_lt_of_eq (by decide : 168 < 176) ht.symm)

/-- A nonprimitive root still has the old semiring DFT meaning. -/
theorem weak_root_erasure (s : Factor) (v : Nat → Nat) (x : s.Data (Expr Nat)) :
    s.reverse.decode (s.reverse.map (Expr.eval v) (s.expressions 1 x)) =
      directDFT 1 (s.decode (s.map (Expr.eval v) x)) :=
  s.expressions_decode 1 (by simp) v x

theorem nonprimitive_twiddle_separator :
    (Factor.comp .two .two).twiddles = 1 ∧ (1 : Nat) ^ (1 * 1) = 1 := by decide

/-- Both lowered realizations retain the ordinary exact Fourier observation. -/
theorem size16_semantics (optimized : Bool) (v : Nat → ℝ)
    (x : (bush 2).Data ComplexWire) :
    (bush 2).reverse.decode ((bush 2).reverse.map (value v)
      (lower optimized (bush 2) [] x)) =
    directDFT (bush 2).fourierRoot ((bush 2).decode ((bush 2).map (value v) x)) :=
  lower_fourier v optimized (bush 2) [] x

end Examples.MeasuredFFT
