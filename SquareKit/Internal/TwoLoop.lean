import SquareKit.DoubleDelooping
import Squares

/-! Algebraic 2-loops with one fixed object and one fixed 1-arrow. This source
has 2-cell variables, identity, vertical/horizontal composition and inverse.
Its equation judgments are strict algebraic laws, not a dependent identity
eliminator or 3-cell witnesses. Ordinary Lean clients can use DoubleDelooping
without this opt-in syntax. -/
namespace SquareKit.Internal.TwoLoop
open DoubleDelooping
universe u v

inductive Expr (ι : Type u) where
  | var : ι → Expr ι
  | unit : Expr ι
  | vertical : Expr ι → Expr ι → Expr ι
  | horizontal : Expr ι → Expr ι → Expr ι
  | inverse : Expr ι → Expr ι

namespace Expr
variable {ι κ : Type u}

def eval {A : Type v} [CommGroup A] (ρ : ι → A) : Expr ι → A
  | .var i => ρ i
  | .unit => 1
  | .vertical p q => DoubleDelooping.vertical A (eval ρ p) (eval ρ q)
  | .horizontal p q => DoubleDelooping.horizontal A (eval ρ p) (eval ρ q)
  | .inverse p => (eval ρ p)⁻¹

def subst (σ : ι → Expr κ) : Expr ι → Expr κ
  | .var i => σ i
  | .unit => .unit
  | .vertical p q => .vertical (subst σ p) (subst σ q)
  | .horizontal p q => .horizontal (subst σ p) (subst σ q)
  | .inverse p => .inverse (subst σ p)

theorem eval_subst {A : Type v} [CommGroup A] (σ : ι → Expr κ)
    (ρ : κ → A) (e : Expr ι) : (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ) := by
  induction e <;> simp_all [subst, eval]

theorem map_eval {A B : Type v} [CommGroup A] [CommGroup B]
    (f : A →* B) (ρ : ι → A) (e : Expr ι) :
    f (e.eval ρ) = e.eval (fun i => f (ρ i)) := by
  induction e <;> simp_all [eval, map_vertical, map_horizontal, map_inv]
end Expr

/-- The supported equations. They do not assert that all 2-loops coincide. -/
inductive Derives {ι : Type u} : Expr ι → Expr ι → Prop
  | refl (p) : Derives p p
  | symm : Derives p q → Derives q p
  | trans : Derives p q → Derives q r → Derives p r
  | vertical : Derives p p' → Derives q q' → Derives (.vertical p q) (.vertical p' q')
  | horizontal : Derives p p' → Derives q q' → Derives (.horizontal p q) (.horizontal p' q')
  | inverse : Derives p q → Derives (.inverse p) (.inverse q)
  | vertical_unit (p) : Derives (.vertical .unit p) p
  | horizontal_unit (p) : Derives (.horizontal .unit p) p
  | vertical_unit_right (p) : Derives (.vertical p .unit) p
  | horizontal_unit_right (p) : Derives (.horizontal p .unit) p
  | vertical_assoc (p q r) :
      Derives (.vertical (.vertical p q) r) (.vertical p (.vertical q r))
  | horizontal_assoc (p q r) :
      Derives (.horizontal (.horizontal p q) r) (.horizontal p (.horizontal q r))
  | vertical_inverse (p) : Derives (.vertical p (.inverse p)) .unit
  | horizontal_inverse (p) : Derives (.horizontal p (.inverse p)) .unit
  | vertical_inverse_left (p) : Derives (.vertical (.inverse p) p) .unit
  | horizontal_inverse_left (p) : Derives (.horizontal (.inverse p) p) .unit
  | interchange (p q r s) :
      Derives (.vertical (.horizontal p q) (.horizontal r s))
        (.horizontal (.vertical p r) (.vertical q s))

/-- Every source law holds in every double delooping supplied here. -/
theorem sound {ι : Type u} {A : Type v} [CommGroup A]
    {p q : Expr ι} (h : Derives p q) (ρ : ι → A) : p.eval ρ = q.eval ρ := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | vertical _ _ ih₁ ih₂ => simp only [Expr.eval, ih₁, ih₂]
  | horizontal _ _ ih₁ ih₂ => simp only [Expr.eval, ih₁, ih₂]
  | inverse _ ih => simp only [Expr.eval, ih]
  | vertical_unit p => exact mul_one _
  | horizontal_unit p => exact mul_one _
  | vertical_unit_right p => exact one_mul _
  | horizontal_unit_right p => exact one_mul _
  | vertical_assoc p q r => exact (mul_assoc _ _ _).symm
  | horizontal_assoc p q r => exact (mul_assoc _ _ _).symm
  | vertical_inverse p => exact DoubleDelooping.vertical_inverse A _
  | horizontal_inverse p => exact DoubleDelooping.horizontal_inverse A _
  | vertical_inverse_left p => exact mul_inv_cancel _
  | horizontal_inverse_left p => exact mul_inv_cancel _
  | interchange p q r s => exact DoubleDelooping.interchange A _ _ _ _

/-- Evaluation through a group homomorphism is an existing representation square. -/
def interpretationSquare {ι A B : Type u} [CommGroup A] [CommGroup B]
    (f : A →* B) (e : Expr ι) :
    Squares.Square ⟨ι → A, ι → B, fun ρ i => f (ρ i)⟩ ⟨A, B, f⟩ where
  impl := fun ρ => e.eval ρ
  spec := fun ρ => e.eval ρ
  commutes := fun ρ => e.map_eval f ρ
end SquareKit.Internal.TwoLoop
