import Applications.Probability.PermutationTail
import Mathlib.Tactic

set_option autoImplicit false

namespace FDSA.TailArithmeticProbe

theorem one_sixth_add_one_sixth : (1 / 6 : ENNReal) + 1 / 6 = 1 / 3 := by
  norm_num [← ENNReal.coe_div]

theorem two_mul_one_sixth : (2 : ENNReal) * (1 / 6) = 1 / 3 := by
  norm_num [← ENNReal.coe_div]

theorem two_mul_one_third : (2 : ENNReal) * (1 / 3) = 2 / 3 := by
  norm_num [← ENNReal.coe_div]

end FDSA.TailArithmeticProbe
