import SquareKit.SmoothQuotient
import Applications.AD.SmoothAlgebras
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental consumers of smooth ordinary-ideal quotients, including a nonpolynomial operation. -/
noncomputable section
open scoped ContDiff
namespace Examples.SmoothQuotient
open SquareKit.SmoothAlgebra

abbrev atZero : Hom (Free 1) ℝ := evaluate (fun _ => 0)
def vanishing : Ideal (Free 1) := RingHom.ker atZero.toAlgHom

/-- The ideal is neither the zero ideal nor the improper ideal. -/
theorem vanishing_nontrivial : vanishing ≠ ⊥ ∧ vanishing ≠ ⊤ := by
  constructor
  · intro h
    have hg : generator (0 : Fin 1) ∈ vanishing := by
      change atZero (generator 0) = 0
      exact evaluate_generator _ _
    rw [h, Ideal.mem_bot] at hg
    have := congrArg (fun f : Free 1 => f.val (fun _ => 1)) hg
    norm_num [generator, projection] at this
  · intro h
    have ho : (1 : Free 1) ∈ vanishing := by rw [h]; trivial
    change atZero.toAlgHom 1 = 0 at ho
    simp at ho

/-- This map is obtained by the general smooth quotient universal property. -/
def value : Hom (Free 1 ⧸ vanishing) ℝ :=
  SquareKit.SmoothAlgebra.Quotient.lift vanishing atZero (fun _ h => h)

def constants : Hom ℝ (Free 1) where
  toFun r := constant 1 r
  map_act _ _ := rfl

def inverse : Hom ℝ (Free 1 ⧸ vanishing) := Hom.comp (Quotient.projection vanishing) constants

theorem value_inverse : Hom.comp value inverse = Hom.ident := Hom.ext fun _ => rfl

theorem inverse_value : Hom.comp inverse value = Hom.ident := by
  apply Quotient.unique vanishing
  apply Hom.ext
  intro f
  apply Ideal.Quotient.eq.mpr
  change atZero.toAlgHom (constants (atZero f) - f) = 0
  rw [map_sub]
  change atZero f - atZero f = 0
  exact sub_self _

/-- An isomorphism of underlying carriers with smooth maps in both directions. -/
def quotientEquiv : (Free 1 ⧸ vanishing) ≃ ℝ where
  toFun := value
  invFun := inverse
  left_inv q := congrArg (fun h : Hom (Free 1 ⧸ vanishing) (Free 1 ⧸ vanishing) => h q) inverse_value
  right_inv r := congrArg (fun h : Hom ℝ ℝ => h r) value_inverse

def exponential : Operation 1 :=
  ⟨fun x => Real.exp (x 0), Real.contDiff_exp.comp (contDiff_apply ℝ _ 0)⟩

theorem exponential_descends : value (Quotient.projection vanishing exponential) = 1 := by
  have h := congrArg (fun k : Hom (Free 1) ℝ => k exponential)
    (Quotient.lift_projection vanishing atZero (fun _ h => h))
  exact h.trans Real.exp_zero

theorem exp_operation (q : Free 1 ⧸ vanishing) :
    (value (show Free 1 ⧸ vanishing from @Structure.act (Free 1 ⧸ vanishing) inferInstance inferInstance inferInstance 1 exponential (fun _ => q))) = Real.exp (value q) := value.map_act _ _

/-- Improper ideals retain the nullary laws in the actual zero ring quotient. -/
theorem improper_nullary (r : ℝ) :
    act (constant 0 r) (Fin.elim0 : Fin 0 → ℝ ⧸ (⊤ : Ideal ℝ)) = 0 := by
  exact Subsingleton.elim _ _

/-- No-coordinate factorization asserts that every function on the singleton input is constant. -/
theorem no_coordinates (f : Operation 0) (x y : Fin 0 → ℝ) : f.val x = f.val y := by
  have h := SquareKit.SmoothHadamard.factorization f.property x y
  exact sub_eq_zero.mp (by simpa using h)

end Examples.SmoothQuotient
