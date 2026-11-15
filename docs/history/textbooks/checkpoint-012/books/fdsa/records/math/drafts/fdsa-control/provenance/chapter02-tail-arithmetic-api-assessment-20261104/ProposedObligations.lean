import Applications.Probability.PermutationTail
import Mathlib.Tactic

-- Source/API proposal only: not executed by the author.
set_option autoImplicit false
set_option warningAsError true

namespace FDSA.TailArithmeticTransferProposal

theorem one_sixth_add_one_sixth : (1 / 6 : ENNReal) + 1 / 6 = 1 / 3 := by
  have h : (1 / 6 : NNReal) + 1 / 6 = 1 / 3 := by norm_num
  have h6 : (6 : NNReal) ≠ 0 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (p := 1) h6,
    ENNReal.coe_div (p := 1) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

theorem two_mul_one_sixth : (2 : ENNReal) * (1 / 6) = 1 / 3 := by
  have h : (2 : NNReal) * (1 / 6) = 1 / 3 := by norm_num
  have h6 : (6 : NNReal) ≠ 0 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (p := 1) h6,
    ENNReal.coe_div (p := 1) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

theorem two_mul_one_third : (2 : ENNReal) * (1 / 3) = 2 / 3 := by
  have h : (2 : NNReal) * (1 / 3) = 2 / 3 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (p := 1) h3,
    ENNReal.coe_div (p := 2) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

end FDSA.TailArithmeticTransferProposal
