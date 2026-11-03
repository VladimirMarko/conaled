import Applications.AD.SecondOrder
import Applications.AD.SecondStage

/-! Experimental smooth operations on the genuine second-order real stage. -/
noncomputable section
open scoped ContDiff
namespace Applications.AD.SmoothSecondStage
open SmoothDual (Operation substitute projection constant addition multiplication)
open SecondOrder SecondStage

def act {n : ℕ} (f : Operation n) (z : Fin n → Stage) : Stage :=
  let p := jet f.val (fun i => (coeff (z i)).1)
    (fun i => (coeff (z i)).2.1) (fun i => (coeff (z i)).2.2)
  ofCoeff p.1 p.2.1 p.2.2

@[simp] theorem coeff_act {n : ℕ} (f : Operation n) (z : Fin n → Stage) :
    coeff (act f z) = jet f.val (fun i => (coeff (z i)).1)
      (fun i => (coeff (z i)).2.1) (fun i => (coeff (z i)).2.2) := coeff_ofCoeff _ _ _

/-- The Hessian convention is explicit at every finite arity. -/
theorem quadratic_coefficient {n : ℕ} (f : Operation n) (x v w : Fin n → ℝ) :
    (coeff (act f (fun i => ofCoeff (x i) (v i) (w i)))).2.2 =
      fderiv ℝ f.val x w + (1/2 : ℝ) * second f.val x v v := by
  simp only [coeff_act, coeff_ofCoeff]
  rfl

theorem act_substitute {m n : ℕ} (f : Operation n) (g : Fin n → Operation m) (z : Fin m → Stage) :
    act (substitute f g) z = act f (fun i => act (g i) z) := by
  apply SecondStage.ext
  simp only [coeff_act]
  have h := jet_comp (fun x i => (g i).val x) f.val
    (contDiff_pi.mpr (fun i => (g i).property)) f.property
    (fun i => (coeff (z i)).1) (fun i => (coeff (z i)).2.1) (fun i => (coeff (z i)).2.2)
  rw [jet_tuple _ (fun i => (g i).property)] at h
  exact h

theorem act_projection {n : ℕ} (i : Fin n) (z : Fin n → Stage) : act (projection i) z = z i := by
  apply SecondStage.ext
  rw [coeff_act]
  exact jet_linear (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) _ _ _

theorem act_constant (n : ℕ) (a : ℝ) (z : Fin n → Stage) :
    act (constant n a) z = algebraMap ℝ Stage a := by
  apply SecondStage.ext
  rw [coeff_act, coeff_scalar]
  exact jet_constant _ _ _ _

theorem act_addition (z : Fin 2 → Stage) : act addition z = z 0 + z 1 := by
  apply SecondStage.ext
  rw [coeff_act, coeff_add]
  exact jet_linear ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
    ContinuousLinearMap.proj 1) _ _ _

/-- Product coefficients computed from analytic first and second derivatives. -/
theorem jet_multiplication (x v w : Fin 2 → ℝ) :
    jet multiplication.val x v w =
      (x 0*x 1, x 0*v 1+v 0*x 1, x 0*w 1+v 0*v 1+w 0*x 1) := by
  let p : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let q : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hd : fderiv ℝ multiplication.val = fun y => y 0 • q + y 1 • p := by
    funext y
    exact ((p.hasFDerivAt).mul q.hasFDerivAt).fderiv
  have hh := ((p.hasFDerivAt (x := x)).smul_const q).add
    ((q.hasFDerivAt (x := x)).smul_const p)
  dsimp [jet, second]
  rw [hd]
  erw [hh.fderiv]
  change (x 0*x 1, x 0*v 1+x 1*v 0,
    (x 0*w 1+x 1*w 0)+(1/2 : ℝ)*((v 0*v 1)+(v 1*v 0))) = _
  apply Prod.ext
  · rfl
  apply Prod.ext <;> ring

theorem act_multiplication (z : Fin 2 → Stage) : act multiplication z = z 0 * z 1 := by
  apply SecondStage.ext
  rw [coeff_act, coeff_mul, jet_multiplication]

/-- Every smooth operation commutes with forgetting its quadratic coefficient. -/
theorem project_act {n : ℕ} (f : Operation n) (z : Fin n → Stage) :
    project (act f z) = SmoothDual.act f (fun i => project (z i)) := by
  rfl

theorem jet_reparam {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x v w : E) (a b : ℝ) :
    jet f x (a • v) (b • v + a^2 • w) =
      ((jet f x v w).1, a*(jet f x v w).2.1,
        b*(jet f x v w).2.1+a^2*(jet f x v w).2.2) := by
  simp only [jet, second, map_add, map_smul, smul_apply,
    smul_eq_mul]
  apply Prod.ext
  · rfl
  apply Prod.ext <;> ring

/-- All real parameter pairs preserve every smooth operation. -/
theorem reparam_act {n : ℕ} (a b : ℝ) (f : Operation n) (z : Fin n → Stage) :
    reparam a b (act f z) = act f (fun i => reparam a b (z i)) := by
  apply SecondStage.ext
  simp only [coeff_reparam, coeff_act]
  exact (jet_reparam f.val (fun i => (coeff (z i)).1)
    (fun i => (coeff (z i)).2.1) (fun i => (coeff (z i)).2.2) a b).symm

end Applications.AD.SmoothSecondStage
