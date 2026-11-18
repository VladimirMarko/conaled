import Applications.Probability.RationalKernel
import Mathlib.Probability.Distributions.Bernoulli
import Examples.FiniteKernelEquality

/-! Native probability authoring, composed coordinate changes and mass recovery. -/
set_option autoImplicit false
set_option warningAsError true
namespace Applications.Probability.RationalKernelExamples
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable def coin (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : RationalKernel Bool Bool where
  kernel := Kernel.const Bool (bernoulliMeasure true false ⟨q,by exact_mod_cast h0,by exact_mod_cast h1⟩)
  markov := inferInstance
  rational x y := by
    cases y
    · refine ⟨1-q,sub_nonneg.mpr h1,?_⟩
      simp only [Kernel.const_apply]
      rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) (by simp)]
      simp only [mass, Rat.cast_sub, Rat.cast_one, unitInterval.toNNReal, unitInterval.symm]
      exact ENNReal.ofReal_eq_coe_nnreal _
    · refine ⟨q,h0,?_⟩
      simp only [Kernel.const_apply]
      rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp)]
      simp only [mass, unitInterval.toNNReal]
      exact ENNReal.ofReal_eq_coe_nnreal _
end Applications.Probability.RationalKernelExamples

namespace Applications.Probability.RationalKernelExamples
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem coin_true (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (x : Bool) :
    (coin q h0 h1).table.entry x true = q := by
  apply RationalKernel.table_entry_eq _ _ _ _ h0
  simp only [coin, Kernel.const_apply]
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp)]
  simp only [mass, unitInterval.toNNReal]
  exact (ENNReal.ofReal_eq_coe_nnreal _).symm

theorem coin_false (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (x : Bool) :
    (coin q h0 h1).table.entry x false = 1-q := by
  apply RationalKernel.table_entry_eq _ _ _ _ (sub_nonneg.mpr h1)
  simp only [coin, Kernel.const_apply]
  rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) (by simp)]
  simp only [mass, Rat.cast_sub, Rat.cast_one, unitInterval.toNNReal, unitInterval.symm]
  exact (ENNReal.ofReal_eq_coe_nnreal _).symm

abbrev liftBits : Bool ≃ ULift.{0} Bool := Equiv.ulift.symm
abbrev unliftSwap : ULift.{0} Bool ≃ Bool := Equiv.ulift.trans (Equiv.swap false true)
noncomputable def thirdCoin := coin (1/3) (by norm_num) (by norm_num)
noncomputable def transportedCoin := (thirdCoin.relabel liftBits liftBits).relabel unliftSwap unliftSwap
example : transportedCoin.table.entry false false = 1/3 := by
  rw [transportedCoin, RationalKernel.relabel_table_entry, RationalKernel.relabel_table_entry]
  exact coin_true _ _ _ _
example : transportedCoin = thirdCoin.relabel (liftBits.trans unliftSwap) (liftBits.trans unliftSwap) :=
  RationalKernel.relabel_trans _ _ _ _ _
example : (coin (1/3) (by norm_num) (by norm_num)).table ≠
    (coin (2/3) (by norm_num) (by norm_num)).table := by
  intro h
  have := congrArg (fun t : Table Bool Bool => t.entry false true) h
  rw [coin_true, coin_true] at this
  norm_num at this
example (x y : Bool) :
    0 < (coin (1/3) (by norm_num) (by norm_num)).table.entry x y ∧
    0 < (coin (2/3) (by norm_num) (by norm_num)).table.entry x y := by
  cases y <;> simp only [coin_true, coin_false] <;> norm_num
end Applications.Probability.RationalKernelExamples

namespace Applications.Probability.Examples
/-- The established direct MH client retains its exact table. -/
example : (FiniteMHExamples.asymmetric.transition : Table bitSpace bitSpace).rationalKernel.table =
    FiniteMHExamples.asymmetric.transition := Table.rationalKernel_table _
end Applications.Probability.Examples
