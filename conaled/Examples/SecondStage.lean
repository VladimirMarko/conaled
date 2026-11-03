import Applications.AD.SmoothSecondStage
import Applications.AD.Jets
import Examples.SmoothDual

/-! Experimental second-order clients: quadratic information, nonpolynomial
analytic coefficients, and loss under the first-order projection. -/
noncomputable section
open scoped ContDiff
namespace Examples.SecondStage
open Applications.AD.SecondStage Applications.AD.SecondOrder
open Applications.AD.SmoothSecondStage
open Applications.AD.SmoothDual (Operation substitute projection constant multiplication)

theorem exp_jet (x v w : ℝ) : jet Real.exp x v w =
    (Real.exp x, Real.exp x * v, Real.exp x * (w+v^2/2)) := by
  let I := ContinuousLinearMap.id ℝ ℝ
  have hd : fderiv ℝ Real.exp = fun y => Real.exp y • I := by
    funext y
    rw [(Real.hasDerivAt_exp y).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro t
    simp [I, mul_comm]
  have hh := (Real.hasDerivAt_exp x).hasFDerivAt.smul_const I
  dsimp [jet, second]
  rw [hd]
  erw [hh.fderiv]
  change (Real.exp x, Real.exp x*v, Real.exp x*w+(1/2:ℝ)*((v*Real.exp x)*v)) = _
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  ring

theorem exp_coeff (x v w : ℝ) :
    coeff (act SmoothDual.exponential (fun _ => ofCoeff x v w)) =
      (Real.exp x, Real.exp x*v, Real.exp x*(w+v^2/2)) := by
  rw [coeff_act]
  simp only [coeff_ofCoeff]
  have h := jet_comp (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ)
    Real.exp (contDiff_apply ℝ (fun _ => ℝ) 0) Real.contDiff_exp
    (fun _ => x) (fun _ => v) (fun _ => w)
  rw [jet_linear, exp_jet] at h
  exact h

/-- The ordinary second derivative is one; the stored coefficient is one half. -/
theorem exp_at_epsilon :
    coeff (act SmoothDual.exponential (fun _ => epsilon)) = (1,1,1/2) := by
  rw [epsilon, exp_coeff]
  norm_num

theorem exp_second_derivative (x : ℝ) :
    HasDerivAt (deriv Real.exp) (Real.exp x) x := by
  simpa only [Real.deriv_exp] using Real.hasDerivAt_exp x

theorem exp_analytic_coefficient (x : ℝ) :
    (coeff (act SmoothDual.exponential (fun _ => ofCoeff x 1 0))).2.2 =
      (1/2 : ℝ) * deriv (deriv Real.exp) x := by
  rw [exp_coeff, (exp_second_derivative x).deriv]
  dsimp
  ring

def square : Operation 1 := substitute multiplication (fun _ => projection 0)

theorem square_coeff (z : Fin 1 → Stage) : coeff (act square z) =
    ((coeff (z 0)).1^2, 2*(coeff (z 0)).1*(coeff (z 0)).2.1,
      (coeff (z 0)).2.1^2+2*(coeff (z 0)).1*(coeff (z 0)).2.2) := by
  rw [square, act_substitute, act_multiplication, act_projection]
  rw [coeff_mul]
  apply Prod.ext
  · ring
  apply Prod.ext <;> ring

/-- Existing polynomial jets certify the ordinary derivative; it is twice the stored coefficient. -/
theorem square_second_derivative : iteratedDeriv 2 (fun x : ℝ => x^2) 0 = 2 := by
  have hp : (fun x : ℝ => ((Polynomial.X : Polynomial ℝ)^2).eval x) = (fun x => x^2) := by
    funext x
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hp, ← Applications.AD.Jets.jet_correct, Applications.AD.Jets.jet_monomial]
  norm_num

theorem square_at_epsilon : act square (fun _ => epsilon) = epsilon^2 := by
  rw [square, act_substitute, act_multiplication, act_projection, pow_two]

theorem square_coefficient_convention :
    (coeff (act square (fun _ => epsilon))).2.2 = 1 ∧
      iteratedDeriv 2 (fun x : ℝ => x^2) 0 = 2 := by
  refine ⟨?_, square_second_derivative⟩
  rw [square_at_epsilon, epsilon_sq]
  simp only [coeff_ofCoeff]

theorem projection_loses_quadratic :
    epsilon^2 ≠ 0 ∧ project (epsilon^2) = project 0 := by
  refine ⟨epsilon_sq_ne_zero, ?_⟩
  rw [epsilon_sq, project_ofCoeff, map_zero]
  rfl

theorem reparam_nonidentity : reparam 2 1 ≠ AlgHom.id ℝ Stage := by
  intro h
  have hh := congrArg (fun k : Stage →ₐ[ℝ] Stage => (coeff (k epsilon)).2.1) h
  rw [coeff_reparam] at hh
  norm_num [epsilon] at hh

theorem reparam_exponential (z : Fin 1 → Stage) :
    reparam 2 1 (act SmoothDual.exponential z) =
      act SmoothDual.exponential (fun i => reparam 2 1 (z i)) := reparam_act _ _ _ _

theorem nullary (f : Operation 0) (z : Fin 0 → Stage) :
    act f z = algebraMap ℝ Stage (f.val Fin.elim0) := by
  have h : f = constant 0 (f.val Fin.elim0) := by
    apply Subtype.ext
    funext x
    exact congrArg f.val (Subsingleton.elim _ _)
  calc
    act f z = act (constant 0 (f.val Fin.elim0)) z := congrArg (fun g => act g z) h
    _ = _ := act_constant _ _ _

end Examples.SecondStage
