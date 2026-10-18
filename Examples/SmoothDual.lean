import Applications.AD.SmoothDual
import Examples.SyntheticProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental real dual-stage clients and the optional source-coefficient comparison. -/

noncomputable section
open scoped ContDiff
open Applications.AD Applications.AD.SmoothDual

namespace Examples.SmoothDual

def exponential : Operation 1 :=
  ⟨fun x => Real.exp (x 0), Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ => ℝ) 0)⟩

theorem exponential_formula (z : Fin 1 → DualNumber ℝ) :
    act exponential z = ⟨Real.exp (z 0).fst, Real.exp (z 0).fst * (z 0).snd⟩ := by
  let d : DMap ℝ ℝ := ⟨Real.exp,
    fun x => ContinuousLinearMap.toSpanSingleton ℝ (Real.exp x),
    fun x => (Real.hasDerivAt_exp x).hasFDerivAt⟩
  rw [act_of_dmap exponential
    (DMap.comp d (DMap.linear (ContinuousLinearMap.proj 0))) (fun _ => rfl)]
  apply TrivSqZeroExt.ext
  · rfl
  · change (z 0).snd * Real.exp (z 0).fst = _
    exact mul_comm _ _

theorem exponential_nonzero_direction :
    act exponential (fun _ => (⟨0, 2⟩ : DualNumber ℝ)) = ⟨1, 2⟩ := by
  erw [exponential_formula]
  apply TrivSqZeroExt.ext <;> simp

theorem nullary (f : Operation 0) (z : Fin 0 → DualNumber ℝ) :
    act f z = algebraMap ℝ (DualNumber ℝ) (f.val Fin.elim0) := by
  have h : f = constant 0 (f.val Fin.elim0) := by
    apply Subtype.ext
    funext x
    exact congrArg f.val (Subsingleton.elim _ _)
  calc
    act f z = act (constant 0 (f.val Fin.elim0)) z := congrArg (fun g => act g z) h
    _ = _ := act_constant _ _ _

theorem zero_arity_substitution (a : ℝ) (z : Fin 0 → DualNumber ℝ) :
    act (substitute addition (fun _ => constant 0 a)) z =
      algebraMap ℝ (DualNumber ℝ) a + algebraMap ℝ (DualNumber ℝ) a := by
  rw [act_substitute, act_addition, act_constant]

theorem multiplication_epsilon :
    act multiplication (fun _ => (DualNumber.eps : DualNumber ℝ)) = 0 := by
  rw [act_multiplication, DualNumber.eps_mul_eps]

/-- Coefficient extension is an actual ring map, not a claimed functor of KL models. -/
def extendIntegers : DualNumber ℤ →+* DualNumber ℝ where
  toFun z := ⟨z.fst, z.snd⟩
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change ((a.fst * b.fst : ℤ) : ℝ) = (a.fst : ℝ) * b.fst
      exact Int.cast_mul _ _
    · change ((a.fst * b.snd + a.snd * b.fst : ℤ) : ℝ) =
        (a.fst : ℝ) * b.snd + (a.snd : ℝ) * b.fst
      simp only [Int.cast_add, Int.cast_mul]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change ((a.fst + b.fst : ℤ) : ℝ) = (a.fst : ℝ) + b.fst
      exact Int.cast_add _ _
    · change ((a.snd + b.snd : ℤ) : ℝ) = (a.snd : ℝ) + b.snd
      exact Int.cast_add _ _

/-- Polynomial stages evaluate through any chosen real dual element. -/
def extendPolynomial (z : DualNumber ℝ) : Polynomial ℤ →+* DualNumber ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom _) z

theorem polynomial_extension (p : Polynomial ℤ) (z : DualNumber ℤ) :
    extendIntegers (p.eval₂ (Int.castRingHom _) z) = extendPolynomial (extendIntegers z) p := by
  rw [Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

def fourth : Operation 1 := ⟨fun x => x 0 ^ 4, (contDiff_apply ℝ (fun _ => ℝ) 0).pow 4⟩

/-- The tangent coefficient is the source-derived model coefficient, evaluated externally. -/
theorem fourth_model_coefficient (z : Fin 1 → DualNumber ℝ) :
    act fourth z = ⟨(z 0).fst ^ 4,
      ((SyntheticProduct.modelCoefficient.map (Int.castRingHom ℝ)).eval (z 0).fst) *
        (z 0).snd⟩ := by
  let d : DMap ℝ ℝ := {
    primal := fun x => x ^ 4
    derivative := fun x => ContinuousLinearMap.toSpanSingleton ℝ
      ((SyntheticProduct.modelCoefficient.map (Int.castRingHom ℝ)).eval x)
    correct := fun x => by
      simpa [SyntheticProduct.polynomial] using (SyntheticProduct.analytic_fourth x).hasFDerivAt }
  rw [act_of_dmap fourth
    (DMap.comp d (DMap.linear (ContinuousLinearMap.proj 0))) (fun _ => rfl)]
  apply TrivSqZeroExt.ext
  · rfl
  · change (z 0).snd * _ = _
    exact mul_comm _ _

theorem fourth_ring (z : Fin 1 → DualNumber ℝ) : act fourth z = z 0 ^ 4 := by
  let sq : Operation 1 := substitute multiplication (fun _ => projection 0)
  have h : fourth = substitute multiplication (fun _ => sq) := by
    apply Subtype.ext
    funext x
    change x 0 ^ 4 = (x 0 * x 0) * (x 0 * x 0)
    ring
  rw [h, act_substitute, act_multiplication]
  simp only [sq, act_substitute, act_multiplication, act_projection]
  ring

/-- The fourth-power operation commutes with extension from the old integer dual stage. -/
theorem fourth_extension (z : DualNumber ℤ) :
    act fourth (fun _ => extendIntegers z) =
      extendIntegers (SyntheticProduct.fourth.hom.app
        (SquareKit.AlgebraicKL.atStage AlgebraicKL.dualIntegers) z) := by
  rw [fourth_ring]
  change extendIntegers z ^ 4 = extendIntegers ((z*z)*(z*z))
  rw [map_mul, map_mul]
  ring

/-- Extending a source-model coefficient agrees with observing the real dual tangent. -/
theorem coefficient_extension (x : ℤ) :
    (act fourth (fun _ => extendIntegers (⟨x, 1⟩ : DualNumber ℤ))).snd =
      ((SyntheticProduct.modelCoefficient.eval x : ℤ) : ℝ) := by
  rw [fourth_model_coefficient]
  change (SyntheticProduct.modelCoefficient.map (Int.castRingHom ℝ)).eval (x : ℝ) * ((1 : ℤ) : ℝ) = _
  rw [Int.cast_one, mul_one, Polynomial.eval_map]
  exact Polynomial.eval₂_hom (p := SyntheticProduct.modelCoefficient) (Int.castRingHom ℝ) x

end Examples.SmoothDual
