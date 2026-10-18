import SquareKit.SmoothFormalLocalizationStage
import SquareKit.SmoothLocalizationFreeComparison
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental formal localization clients preserving actual nilpotents.
The same dual presentation is localized at a unit and at a nilpotent; their outcomes differ. -/
noncomputable section
open scoped ContDiff
namespace Examples.SmoothFormalLocalization
open SquareKit.SmoothAlgebra
open PresentedLocalization
attribute [local instance] DualExtension.smoothStructure

abbrev x : Free 1 := generator 0
def relations : Fin 1 → Free 1 := ![x^2]
abbrev A := Presentation.Carrier relations
def epsilon : A := Presentation.projection relations x

theorem epsilon_square : epsilon * epsilon = 0 := by
  have h := Presentation.relation_zero relations 0
  change (Presentation.projection relations).toAlgHom (x^2) = 0 at h
  rw [map_pow,pow_two] at h
  exact h

def value : Hom A (DualNumber ℝ) :=
  SquareKit.SmoothAlgebra.Quotient.lift (Presentation.ideal relations) (evaluate (fun _ : Fin 1 => DualNumber.eps)) (by
    have hi : Presentation.ideal relations ≤ RingHom.ker (evaluate (fun _ : Fin 1 => (DualNumber.eps : DualNumber ℝ))).toAlgHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      fin_cases i
      change (evaluate (fun _ : Fin 1 => (DualNumber.eps : DualNumber ℝ))).toAlgHom (x^2) = 0
      rw [map_pow]
      change (evaluate (fun _ : Fin 1 => (DualNumber.eps : DualNumber ℝ)) (generator 0))^2 = 0
      rw [evaluate_generator,DualNumber.eps_pow_two]
    exact fun p hp => hi hp)

theorem value_epsilon : value epsilon = DualNumber.eps := by
  change evaluate (fun _ : Fin 1 => (DualNumber.eps : DualNumber ℝ)) (generator 0) = DualNumber.eps
  exact evaluate_generator _ _

theorem epsilon_nonzero : epsilon ≠ 0 := by
  intro h
  have he := congrArg (fun z => (value.toAlgHom z).snd) h
  change (value epsilon).snd = (value.toAlgHom 0).snd at he
  rw [value_epsilon,map_zero] at he
  exact one_ne_zero (show (1 : ℝ)=0 from he)

def unitPolynomial : Free 1 := 1+x

theorem unit_value : IsUnit (Presentation.projection relations unitPolynomial) := by
  change IsUnit ((Presentation.projection relations).toAlgHom (1+x))
  rw [map_add,map_one]
  exact (show IsNilpotent epsilon from ⟨2,by simpa only [pow_two] using epsilon_square⟩).isUnit_one_add

theorem unit_localization_inverse : Hom.comp (base relations unitPolynomial) (unitRetraction relations unitPolynomial unit_value) = Hom.ident :=
  unit_inverse_base _ _ _

theorem unit_preserves_epsilon : base relations unitPolynomial epsilon ≠ 0 := by
  intro h
  have hi := congrArg (fun k : Hom A A => k epsilon) (unit_base_inverse relations unitPolynomial unit_value)
  change unitRetraction relations unitPolynomial unit_value (base relations unitPolynomial epsilon) = epsilon at hi
  rw [h] at hi
  have hz : unitRetraction relations unitPolynomial unit_value 0 = 0 := (unitRetraction relations unitPolynomial unit_value).toAlgHom.map_zero
  rw [hz] at hi
  exact epsilon_nonzero hi.symm

theorem nilpotent_localization_trivial : Subsingleton (Carrier relations x) :=
  nilpotent_subsingleton relations x ⟨2,by change epsilon^2=0; rw [pow_two]; exact epsilon_square⟩

def scaling : Hom A A :=
  SquareKit.SmoothAlgebra.Quotient.lift (Presentation.ideal relations) (evaluate (fun _ : Fin 1 => epsilon+epsilon)) (by
    have hi : Presentation.ideal relations ≤ RingHom.ker (evaluate (fun _ : Fin 1 => epsilon+epsilon)).toAlgHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      fin_cases i
      change (evaluate (fun _ : Fin 1 => epsilon+epsilon)).toAlgHom (x^2) = 0
      rw [map_pow]
      change (evaluate (fun _ : Fin 1 => epsilon+epsilon) (generator 0))^2=0
      rw [evaluate_generator,pow_two]
      simp [add_mul,mul_add,epsilon_square]
    exact fun p hp => hi hp)

theorem scaling_epsilon : scaling epsilon = epsilon+epsilon := evaluate_generator _ _

theorem scaling_nonidentity : scaling ≠ Hom.ident := by
  intro h
  have he := congrArg (fun k : Hom A A => value (k epsilon)) h
  change value (scaling epsilon) = value epsilon at he
  rw [scaling_epsilon,value.map_add,value_epsilon] at he
  have hs := congrArg TrivSqZeroExt.snd he
  change (1 : ℝ)+1=1 at hs
  norm_num at hs

def exponential : Free 1 := ⟨fun z => Real.exp (z 0), by
  change ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => Real.exp (z 0))
  exact Real.contDiff_exp.comp (contDiff_apply ℝ _ 0)⟩

theorem exponential_value_unit : IsUnit (value (Presentation.projection relations exponential)) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  change IsUnit (Real.exp 0)
  rw [Real.exp_zero]
  exact isUnit_one

def exponentialDualPoint : Hom (Carrier relations exponential) (DualNumber ℝ) :=
  lift relations exponential value exponential_value_unit

theorem exponentialDualPoint_base : Hom.comp exponentialDualPoint (base relations exponential) = value :=
  lift_base relations exponential value exponential_value_unit

theorem representatives_equal : Presentation.projection relations exponential = Presentation.projection relations (exponential+x^2) := by
  change (Presentation.projection relations).toAlgHom exponential = (Presentation.projection relations).toAlgHom (exponential+x^2)
  rw [map_add]
  have h : (Presentation.projection relations).toAlgHom (x^2) = 0 := Presentation.relation_zero relations 0
  rw [h,add_zero]

theorem nonpolynomial_comparison :
    Hom.comp (compare relations (exponential+x^2) exponential representatives_equal.symm)
      (compare relations exponential (exponential+x^2) representatives_equal) = Hom.ident :=
  compare_inverse _ _ _ _

/-- Arbitrary Hom, chosen quotient element, and arbitrary smooth target all appear in this client. -/
theorem scaling_pushout {C : Type*} [CommRing C] [Algebra ℝ C] [Structure C]
    (u : Hom (At relations (Presentation.projection relations exponential)) C) (v : Hom A C)
    (hc : Hom.comp u (atBase relations (Presentation.projection relations exponential)) = Hom.comp v scaling) :
    ∃! k : Hom (At relations (scaling (Presentation.projection relations exponential))) C,
      Hom.comp k (atMap relations (Presentation.projection relations exponential) relations scaling) = u ∧
      Hom.comp k (atBase relations (scaling (Presentation.projection relations exponential))) = v :=
  stage_pushout relations _ relations scaling u v hc

theorem dual_localization_comparison :
    Hom.comp (toLocalizedDual relations unitPolynomial) (fromLocalizedDual relations unitPolynomial) = Hom.ident :=
  dual_localized_inverse _ _

theorem dual_factorization {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
    (h : Hom (DualNumber A) B) :
    Hom.comp (dualLift relations unitPolynomial h
      (unit_value.map (Hom.comp h DualExtension.inclusion).toAlgHom)) (dualBase relations unitPolynomial) = h :=
  dualLift_base _ _ _ _

theorem dual_generator_comparison :
    fromLocalizedDual relations unitPolynomial DualNumber.eps =
      base (Presentation.relations relations (Presentation.dualEquation 1))
        (Localization.extend (k := 1) unitPolynomial) (Presentation.dualEps relations) :=
  fromLocalizedDual_eps _ _

theorem ordinary_open_specialization : Hom.comp (freeToOpen exponential) (openToFree exponential) = Hom.ident :=
  open_free_inverse exponential

theorem zero_localization : Subsingleton (Carrier relations (0 : Free 1)) := by
  apply nilpotent_subsingleton
  change IsNilpotent ((Presentation.projection relations).toAlgHom 0)
  rw [map_zero]
  exact ⟨1,by simp⟩

theorem improper_presentation : Subsingleton (Presentation.Carrier (fun _ : Fin 1 => (1 : Free 0))) := by
  apply subsingleton_of_zero_eq_one
  have h := Presentation.relation_zero (fun _ : Fin 1 => (1 : Free 0)) 0
  change (Presentation.projection (fun _ : Fin 1 => (1 : Free 0))).toAlgHom 1 = 0 at h
  rw [map_one] at h
  exact h.symm

end Examples.SmoothFormalLocalization
