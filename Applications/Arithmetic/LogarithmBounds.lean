import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Shared base-two logarithm bounds

These ordinary real inequalities retain the positive-input statements of
`Lemmas_log.ld_sum_inequality` and `Lemmas_log.ld_ld_1_less`, used by the
pairing-heap and splay analyses. See `docs/research/fdsa-logarithm-bounds.md`
for the exact manuscript/AFP provenance, consumer boundaries and complete
applicable source notice. These scalar laws make no algorithm-cost claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Arithmetic.LogarithmBounds

/-- The sharp two-input bound, valid also when positive inputs are below one. -/
theorem logb_two_sum_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 x + Real.logb 2 y + 2 ≤ 2 * Real.logb 2 (x + y) := by
  have hbase : (1 : ℝ) < 2 := by norm_num
  have htwo : (0 : ℝ) < 2 := lt_trans zero_lt_one hbase
  have htwo_ne : (2 : ℝ) ≠ 0 := ne_of_gt htwo
  have hx2 : 0 < 2 * x := mul_pos htwo hx
  have hy2 : 0 < 2 * y := mul_pos htwo hy
  have hproduct : (2 * x) * (2 * y) ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have hlog := Real.logb_le_logb_of_le hbase (mul_pos hx2 hy2) hproduct
  rw [Real.logb_mul (ne_of_gt hx2) (ne_of_gt hy2),
    Real.logb_mul htwo_ne (ne_of_gt hx),
    Real.logb_mul htwo_ne (ne_of_gt hy), Real.logb_pow] at hlog
  linarith [Real.logb_self_eq_one hbase]

/-- Removing one unit of the sharp margin gives strictness without distinctness. -/
theorem logb_two_sum_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 + Real.logb 2 x + Real.logb 2 y < 2 * Real.logb 2 (x + y) := by
  have hsharp := logb_two_sum_bound hx hy
  linarith

end Arithmetic.LogarithmBounds
