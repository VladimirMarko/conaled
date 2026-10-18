import Applications.AD.Core
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth maps enter the existing analytic AD interface through their unique derivative. -/

noncomputable section
open scoped ContDiff
namespace Applications.AD.DMap

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness supplies the derivative invariant; no derivative is postulated. -/
def ofSmooth (f : E → F) (hf : ContDiff ℝ ∞ f) : DMap E F where
  primal := f
  derivative := fderiv ℝ f
  correct x := (hf.differentiable (by simp) x).hasFDerivAt

/-- Simultaneous outputs, including the empty tuple. -/
def tuple {n : ℕ} (f : Fin n → DMap E ℝ) : DMap E (Fin n → ℝ) where
  primal x i := (f i).primal x
  derivative x := ContinuousLinearMap.pi (fun i => (f i).derivative x)
  correct x := hasFDerivAt_pi.mpr (fun i => (f i).correct x)

end Applications.AD.DMap
