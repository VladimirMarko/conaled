import SquareKit.SmoothDualExtension

/-! Experimental principal smooth presentation of the real dual algebra. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.DualExtension
attribute [local instance] smoothStructure

def squareIdeal : Ideal (Free 1) := Ideal.span ({(generator (0 : Fin 1)) ^ 2} : Set (Free 1))
def dualEvaluation : Hom (Free 1) (DualNumber ℝ) := evaluate (fun _ => DualNumber.eps)

theorem dualEvaluation_coefficients (f : Free 1) :
    dualEvaluation f = ⟨f.val (fun _ => 0), (derivative f 0).val (fun _ => 0)⟩ := by
  apply TrivSqZeroExt.ext
  · rfl
  · change (∑ i : Fin 1, (derivative f i).val (fun _ => 0) * 1) = _
    simp

/-- Actual smooth divisibility by x² after subtracting value and first derivative. -/
theorem univariate_remainder (f : Free 1) :
    f - realHom (f.val (fun _ => 0)) - generator 0 * realHom ((derivative f 0).val (fun _ => 0)) ∈ squareIdeal := by
  have h := taylor_remainder (Ideal.span ({generator (0 : Fin 1)} : Set (Free 1)))
    (show Operation 1 from f) (fun i => generator i) (fun _ => 0)
    (fun i => by fin_cases i; simp)
  rw [Ideal.span_singleton_mul_span_singleton] at h
  have hv : act (show Operation 1 from f) (fun _ : Fin 1 => (0 : Free 1)) =
      realHom (f.val (fun _ => 0)) := rfl
  have hd : act (derivative f 0) (fun _ : Fin 1 => (0 : Free 1)) =
      realHom ((derivative f 0).val (fun _ => 0)) := rfl
  simpa only [generators_generate, hv, Fin.sum_univ_one, sub_zero, hd, squareIdeal, pow_two] using h

theorem dualEvaluation_kernel (f : Free 1) : dualEvaluation f = 0 ↔ f ∈ squareIdeal := by
  constructor
  · intro h
    have h0 := congrArg TrivSqZeroExt.fst h
    have h1 := congrArg TrivSqZeroExt.snd h
    rw [dualEvaluation_coefficients] at h0 h1
    change f.val (fun _ => 0) = 0 at h0
    change (derivative f 0).val (fun _ => 0) = 0 at h1
    have hr := univariate_remainder f
    rw [h0, h1] at hr
    simpa only [show (realHom : Hom ℝ (Free 1)) 0 = 0 by change algebraMap ℝ (Free 1) 0 = 0; simp,
      mul_zero, sub_zero] using hr
  · intro hf
    have hi : squareIdeal ≤ RingHom.ker dualEvaluation.toAlgHom := by
      apply Ideal.span_le.mpr
      intro g hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      change dualEvaluation.toAlgHom ((generator 0)^2) = 0
      rw [map_pow]
      change dualEvaluation (generator 0)^2=0
      rw [show dualEvaluation (generator 0) = DualNumber.eps from evaluate_generator _ _]
      exact DualNumber.eps_pow_two
    exact hi hf

def presentationValue : Hom (Free 1 ⧸ squareIdeal) (DualNumber ℝ) :=
  Quotient.lift squareIdeal dualEvaluation (fun f hf => (dualEvaluation_kernel f).mpr hf)

def quotientEps : Free 1 ⧸ squareIdeal := Quotient.projection squareIdeal (generator 0)

theorem quotientEps_square : quotientEps * quotientEps = 0 := by
  change Ideal.Quotient.mk squareIdeal (generator 0) * Ideal.Quotient.mk squareIdeal (generator 0) = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp [pow_two])

def presentationInverse : Hom (DualNumber ℝ) (Free 1 ⧸ squareIdeal) :=
  lift realHom quotientEps quotientEps_square

theorem presentationValue_inverse : Hom.comp presentationValue presentationInverse = Hom.ident := by
  apply realHomEquiv.injective
  apply Subtype.ext
  change presentationValue (presentationInverse DualNumber.eps) = DualNumber.eps
  rw [show presentationInverse DualNumber.eps = quotientEps from lift_eps _ _ _]
  exact evaluate_generator (fun _ : Fin 1 => (DualNumber.eps : DualNumber ℝ)) 0

theorem presentationInverse_value : Hom.comp presentationInverse presentationValue = Hom.ident := by
  apply Quotient.unique squareIdeal
  apply hom_ext_generators
  intro i
  fin_cases i
  change presentationInverse (dualEvaluation (generator 0)) = quotientEps
  rw [show dualEvaluation (generator 0) = DualNumber.eps from evaluate_generator _ _]
  exact lift_eps _ _ _

def presentationEquiv : (Free 1 ⧸ squareIdeal) ≃ DualNumber ℝ where
  toFun := presentationValue
  invFun := presentationInverse
  left_inv q := congrArg (fun h : Hom (Free 1 ⧸ squareIdeal) (Free 1 ⧸ squareIdeal) => h q) presentationInverse_value
  right_inv z := congrArg (fun h : Hom (DualNumber ℝ) (DualNumber ℝ) => h z) presentationValue_inverse

end SquareKit.SmoothAlgebra.DualExtension
