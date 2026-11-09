import Mathlib.Algebra.Group.Prod
import SquareKit.Internal.ModalHigher.Keys
import SquareKit.Internal.ModalHigher.Access
import SquareKit.Internal.ModalHigher.Direct

/-! Integer discriminators for the restricted higher-family key diagram. -/
namespace Examples.ModalHigher
open CategoryTheory Bicategory SquareKit.Internal.ModalHigher
open SquareKit.Internal.PathTransport

/-- Inputs 1 in three locked families give 1, 2 and 6. -/
theorem selected_locked :
    observe (multiplier (G := ℤ) 1) 1 = 1 ∧
    observe (multiplier (G := ℤ) 2) 1 = 2 ∧
    observe (multiplier (G := ℤ) 6) 1 = 6 := by
  simp only [observe_eq]
  decide

theorem successive_keys :
    (key (G := ℤ) 3).comp (key 2) = key 6 := key_comp 2 3

/-- One full-context input instead appears as 1, 3, 6 in w, v, u. -/
theorem same_full_input (b : Bool) :
    Multiplicative.toAdd ((view ℤ 1).map₂ (fullCell ℤ b 1)) = 1 ∧
    Multiplicative.toAdd ((view ℤ 3).map₂ (fullCell ℤ b 1)) = 3 ∧
    Multiplicative.toAdd ((view ℤ 6).map₂ (fullCell ℤ b 1)) = 6 := by
  repeat rw [view_cell]
  decide

theorem reflexive_control (d : ℤ) : observe (multiplier (G := ℤ) d) 0 = 0 :=
  zsmul_zero d

theorem forgotten_pullback_rejected :
    observe (multiplier (G := ℤ) 1) 1 ≠ observe (multiplier 2) 1 := by decide

theorem cell_erasure_rejected :
    observe (multiplier (G := ℤ) 2) 0 ≠ observe (multiplier 2) 1 := by decide

def validBoundary : BoundaryCell (multiplier (G := ℤ) 2) 2 0 := ⟨1, rfl⟩

/-- The intended nonzero total cell actually exists. -/
def validCell : totalArrow (multiplier (G := ℤ) 2) 2 ⟶
    totalArrow (multiplier (G := ℤ) 2) 0 := encode validBoundary

theorem correct_lift :
    Multiplicative.toAdd ((lift (multiplier (G := ℤ) 2)).map₂ validCell).base = 2 := rfl

/-- Keeping base label 1 in E₁ would violate the dependent boundary. -/
theorem invalid_boundary : ¬ ∃ p : totalArrow (multiplier (G := ℤ) 1) 2 ⟶
    totalArrow (multiplier (G := ℤ) 1) 0, Multiplicative.toAdd p.base = 1 := by
  rintro ⟨p, hp⟩
  have h := (decode p).boundary
  change (2 : ℤ) = 0 + 1 • Multiplicative.toAdd p.base at h
  rw [hp] at h
  contradiction

theorem locked_boolean_substitution :
    ¬ Factors ℤ (fun b (_ : ℤ) => if b then (1 : ℤ) else 0) :=
  dependent_substitution_rejected ℤ 1 (by decide)

theorem hidden_boolean : ¬ Factors ℤ (fun b (_ : ℤ) => b) :=
  hidden_recovery_rejected ℤ

theorem actual_locked_boolean_substitution :
    ¬ ∃ σ : StrictPseudofunctor (Full ℤ) (Base ℤ), Allowed ℤ σ ∧
      ∀ b, Multiplicative.toAdd (σ.map₂ (fullCell ℤ b 1)) = if b then (1 : ℤ) else 0 :=
  allowed_boolean_choice_rejected ℤ 1 (by decide)

/-- The view triangle checks all dimensions, with the required u ← v ← w direction. -/
theorem view_triangle : (view ℤ 3).comp (key 2) = view ℤ 6 := view_key ℤ 3 2

/-- A negative multiplier is admitted; positivity is not a hidden hypothesis. -/
theorem negative_key : observe (multiplier (G := ℤ) (-2)) 3 = -6 := by decide

/-- Different base and fiber groups expose accidental replacement of BH by BG. -/
def diagonal : ℤ →+ ℤ × ℤ where
  toFun n := (n, n)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem different_group_observation : observe diagonal 1 = (1, 1) := rfl

theorem retains_target_fiber_arrow :
    ((lift diagonal).map (totalArrow diagonal (7, -4))).fiber =
      Discrete.mk (Multiplicative.ofAdd ((7, -4) : ℤ × ℤ)) := lift_arrow diagonal _

end Examples.ModalHigher
