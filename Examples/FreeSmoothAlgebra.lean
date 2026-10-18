import Applications.AD.SmoothAlgebras
import Examples.SecondStage

/-! Experimental consumers of free smooth-algebra evaluation, including nonpolynomial stages. -/
noncomputable section
namespace Examples.FreeSmoothAlgebra
open SquareKit.SmoothAlgebra
open Applications.AD.SmoothAlgebras

abbrev exponential : Free 1 := SmoothDual.exponential

/-- Any interpretation with the specified generator has the analytic dual coefficients. -/
theorem dual_universal_exp (h : Hom (Free 1) (DualNumber ℝ)) (x v : ℝ)
    (hx : h (generator 0) = (⟨x,v⟩ : DualNumber ℝ)) :
    h exponential = (⟨Real.exp x, Real.exp x*v⟩ : DualNumber ℝ) := by
  have he := evaluate_unique h
  have ht : (fun i : Fin 1 => h (generator i)) = fun _ => (⟨x,v⟩ : DualNumber ℝ) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hx
  rw [ht] at he
  rw [← he]
  change act (A := DualNumber ℝ) SmoothDual.exponential (fun _ => (⟨x,v⟩ : DualNumber ℝ)) = _
  erw [dual_act]
  exact SmoothDual.exponential_formula _

/-- Universal second-order evaluation agrees with the analytic Hessian coefficient. -/
theorem second_universal_exp
    (h : Hom (Free 1) Applications.AD.SecondStage.Stage) (x v w : ℝ)
    (hx : h (generator 0) = Applications.AD.SecondStage.ofCoeff x v w) :
    Applications.AD.SecondStage.coeff (h exponential) =
      (Real.exp x,Real.exp x*v,Real.exp x*(w+v^2/2)) := by
  have he := evaluate_unique h
  have ht : (fun i : Fin 1 => h (generator i)) =
      fun _ => Applications.AD.SecondStage.ofCoeff x v w := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hx
  rw [ht] at he
  rw [← he]
  exact SecondStage.exp_coeff x v w

/-- A concrete evaluation, obtained through the universal theorem. -/
theorem evaluate_second_exp :
    Applications.AD.SecondStage.coeff
      (evaluate (fun _ : Fin 1 => Applications.AD.SecondStage.epsilon) exponential) = (1,1,1/2) := by
  have h := second_universal_exp
    (evaluate (fun _ : Fin 1 => Applications.AD.SecondStage.epsilon)) 0 1 0
    (evaluate_generator _ 0)
  simpa using h

/-- The nullary free algebra has exactly one smooth interpretation into any target. -/
theorem nullary_unique {A : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
    (h k : Hom (Free 0) A) : h = k := hom_ext_generators h k (fun i => Fin.elim0 i)

theorem nullary_constant {A : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
    (a : ℝ) : evaluate (A := A) (n := 0) Fin.elim0 (show Free 0 from constant 0 a) =
      algebraMap ℝ A a := Structure.constant _ _ _

/-- Pullback by the nonidentity coordinate map x ↦ exp x. -/
theorem exponential_pullback_nonidentity :
    pullback (fun _ : Fin 1 => SmoothDual.exponential) ≠ (Hom.ident : Hom (Free 1) (Free 1)) := by
  intro h
  have hh := congrArg (fun k : Hom (Free 1) (Free 1) => (k (generator 0)).val (fun _ => 0)) h
  rw [pullback_generator] at hh
  norm_num [exponential, SmoothDual.exponential, Hom.ident, generator, projection] at hh
  change (1 : ℝ) = 0 at hh
  norm_num at hh

/-- Coordinate substitution and interpretation commute even for nonpolynomial coordinates. -/
theorem exponential_pullback_evaluation {A : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
    (a : Fin 1 → A) (f : Free 1) :
    evaluate a (pullback (fun _ : Fin 1 => SmoothDual.exponential) f) =
      evaluate (fun _ : Fin 1 => act SmoothDual.exponential a) f :=
  congrArg (fun h : Hom (Free 1) A => h f)
    (evaluate_pullback (fun _ : Fin 1 => SmoothDual.exponential) a)

end Examples.FreeSmoothAlgebra
