import SquareKit.SmoothDualPresentation
import Applications.AD.SmoothAlgebras
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental non-real clients of the smooth dual coproduct and its presentation. -/
noncomputable section
open scoped ContDiff
namespace Examples.SmoothDualExtension
open SquareKit.SmoothAlgebra SquareKit.SmoothAlgebra.DualExtension
attribute [local instance] smoothStructure

def exponential : Operation 1 :=
  ⟨fun x => Real.exp (x 0), Real.contDiff_exp.comp (contDiff_apply ℝ _ 0)⟩

theorem exponential_derivative : derivative exponential 0 = exponential := by
  apply Subtype.ext
  funext x
  have h := ((Real.hasDerivAt_exp (x 0)).hasFDerivAt.comp x
    (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt).fderiv
  change fderiv ℝ (fun x : Fin 1 → ℝ => Real.exp (x 0)) x (Pi.single 0 1) = Real.exp (x 0)
  erw [h]
  simp

theorem exp_dual (z : DualNumber ℝ) :
    operation exponential (fun _ => z) = ⟨Real.exp z.fst, Real.exp z.fst * z.snd⟩ := by
  apply TrivSqZeroExt.ext
  · rfl
  · change (∑ i : Fin 1, (derivative exponential i).val (fun _ => z.fst) * z.snd) = _
    simp only [Fin.sum_univ_one, exponential_derivative]
    rfl

abbrev Stage := DualNumber (DualNumber ℝ)

/-- Exponential in a dual extension of a non-real infinitesimal base. -/
theorem iterated_exp : operation exponential
    (fun _ => (⟨DualNumber.eps, 1⟩ : Stage)) = ⟨1 + DualNumber.eps, 1 + DualNumber.eps⟩ := by
  apply TrivSqZeroExt.ext
  · change operation exponential (fun _ => (DualNumber.eps : DualNumber ℝ)) = _
    rw [exp_dual]
    apply TrivSqZeroExt.ext <;> simp
  · change differential exponential (fun _ => (DualNumber.eps : DualNumber ℝ)) (fun _ => 1) = _
    simp only [differential, Fin.sum_univ_one, exponential_derivative, mul_one]
    change operation exponential (fun _ => (DualNumber.eps : DualNumber ℝ)) = _
    rw [exp_dual]
    apply TrivSqZeroExt.ext <;> simp

theorem outer_eps_nonzero : (DualNumber.eps : Stage) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : Stage => z.snd.fst) h
  norm_num at h1

/-- A nonidentity target map: double the infinitesimal generator. -/
def scale : Hom (DualNumber ℝ) (DualNumber ℝ) :=
  lift realHom (DualNumber.eps + DualNumber.eps) (by
    simp [add_mul, mul_add, DualNumber.eps_mul_eps])

theorem scale_not_ident : scale ≠ Hom.ident := by
  intro h
  have he := congrArg (fun k : Hom (DualNumber ℝ) (DualNumber ℝ) => (k DualNumber.eps).snd) h
  have hs : scale DualNumber.eps = DualNumber.eps + DualNumber.eps := lift_eps _ _ _
  rw [hs] at he
  change (1 : ℝ) + 1 = 1 at he
  norm_num at he

/-- Naturality of the new universal map under the nonidentity target map. -/
theorem universal_scale (h : Hom ℝ (DualNumber ℝ)) (d : DualNumber ℝ) (hd : d*d=0) :
    Hom.comp scale (lift h d hd) = lift (Hom.comp scale h) (scale d)
      (by change scale.toAlgHom d * scale.toAlgHom d = 0; rw [← map_mul, hd, map_zero]) :=
  lift_natural scale h d hd

/-- The generic coefficient is the old real analytic derivative, for every operation. -/
theorem analytic_coefficient {n : ℕ} (f : Operation n) (x v : Fin n → ℝ) :
    differential f x v = fderiv ℝ f.val x v := (linear_coordinates _ _).symm

/-- The presentation's smooth map sends its nonzero quotient generator to ε. -/
theorem quotient_generator : presentationValue quotientEps = (DualNumber.eps : DualNumber ℝ) :=
  evaluate_generator (fun _ : Fin 1 => (DualNumber.eps : DualNumber ℝ)) 0

theorem zero_arity (f : Operation 0) (d : Stage) (hd : d*d=0) :
    @Structure.act Stage inferInstance inferInstance inferInstance 0 f Fin.elim0 =
      @Structure.act Stage inferInstance inferInstance inferInstance 0 f Fin.elim0 +
        d * differential f (Fin.elim0 : Fin 0 → Stage) Fin.elim0 := by
  have h := nilsquare_taylor f (Fin.elim0 : Fin 0 → Stage) Fin.elim0 d hd
  have he : (fun i : Fin 0 => (Fin.elim0 i : Stage) + d * Fin.elim0 i) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  rw [he] at h
  exact h


/-- The same Taylor theorem specializes to the trivial ordinary quotient algebra. -/
theorem trivial_taylor {n : ℕ} (f : Operation n)
    (x v : Fin n → ℝ ⧸ (⊤ : Ideal ℝ)) (d : ℝ ⧸ (⊤ : Ideal ℝ)) :
    @Structure.act _ inferInstance inferInstance inferInstance n f (fun i => x i + d*v i) =
      @Structure.act _ inferInstance inferInstance inferInstance n f x +
        d * differential f x v := nilsquare_taylor f x v d (Subsingleton.elim _ _)

end Examples.SmoothDualExtension
