import SquareKit.Internal.Cubical.Dimensions
import Mathlib.Data.Fintype.Prod

/-! A finite De Morgan model separates dimension expressions that Boolean
valuation would collapse. These are dimension tests, not higher identity tests. -/
namespace SquareKit.Cubical

namespace Four
abbrev Carrier := Bool × Bool

def neg (x : Carrier) : Carrier := (!x.2, !x.1)
def meet (x y : Carrier) : Carrier := (x.1 && y.1, x.2 && y.2)
def join (x y : Carrier) : Carrier := (x.1 || y.1, x.2 || y.2)

def eval (ρ : α → Carrier) : Expr α → Carrier
  | .zero => (false, false)
  | .one => (true, true)
  | .var a => ρ a
  | .neg a => neg (eval ρ a)
  | .meet a b => meet (eval ρ a) (eval ρ b)
  | .join a b => join (eval ρ a) (eval ρ b)

/-- Soundness for the entire generating congruence, not selected expressions. -/
theorem sound (ρ : α → Carrier) (h : Expr.Conv a b) : eval ρ a = eval ρ b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | neg _ ih => exact congrArg neg ih
  | meet _ _ ih ih' => exact congrArg₂ meet ih ih'
  | join _ _ ih ih' => exact congrArg₂ join ih ih'
  | meet_comm a b => exact (by decide : ∀ x y, meet x y = meet y x) _ _
  | meet_assoc a b c => exact (by decide : ∀ x y z, meet (meet x y) z = meet x (meet y z)) _ _ _
  | meet_idem a => exact (by decide : ∀ x, meet x x = x) _
  | meet_one a => exact (by decide : ∀ x, meet x (true, true) = x) _
  | meet_zero a => exact (by decide : ∀ x, meet x (false, false) = (false, false)) _
  | join_comm a b => exact (by decide : ∀ x y, join x y = join y x) _ _
  | join_assoc a b c => exact (by decide : ∀ x y z, join (join x y) z = join x (join y z)) _ _ _
  | join_idem a => exact (by decide : ∀ x, join x x = x) _
  | join_zero a => exact (by decide : ∀ x, join x (false, false) = x) _
  | join_one a => exact (by decide : ∀ x, join x (true, true) = (true, true)) _
  | absorb_meet a b => exact (by decide : ∀ x y, meet x (join x y) = x) _ _
  | absorb_join a b => exact (by decide : ∀ x y, join x (meet x y) = x) _ _
  | distrib_meet a b c => exact (by decide : ∀ x y z,
      meet x (join y z) = join (meet x y) (meet x z)) _ _ _
  | distrib_join a b c => exact (by decide : ∀ x y z,
      join x (meet y z) = meet (join x y) (join x z)) _ _ _
  | neg_neg a => exact (by decide : ∀ x, neg (neg x) = x) _
  | neg_zero => rfl
  | neg_one => rfl
  | neg_meet a b => exact (by decide : ∀ x y, neg (meet x y) = join (neg x) (neg y)) _ _
  | neg_join a b => exact (by decide : ∀ x y, neg (join x y) = meet (neg x) (neg y)) _ _

@[simp] theorem eval_subst (ρ : β → Carrier) (σ : α → Expr β) (a : Expr α) :
    eval ρ (Expr.subst σ a) = eval (fun x => eval ρ (σ x)) a := by
  induction a <;> simp_all [Expr.subst, eval]

end Four

/-- Boolean complementation is not valid dimension conversion. -/
theorem dimension_not_boolean :
    ¬ Expr.Conv (.meet (.var ()) (.neg (.var ()))) (.zero : Expr Unit) := by
  intro h
  have bad := Four.sound (fun _ => (true, false)) h
  cases bad

/-- Even the Kleene inequality is not imposed on independent dimensions.
Its meet-form would assert `i ∧ ¬i ≤ j ∨ ¬j`. -/
theorem dimensions_not_kleene :
    ¬ Expr.Conv
      (.meet (.meet (.var false) (.neg (.var false)))
        (.join (.var true) (.neg (.var true))))
      (.meet (.var false) (.neg (.var false))) := by
  intro h
  have bad := Four.sound (fun b => if b then (false, true) else (true, false)) h
  cases bad

/-- The rejection survives passing to actual cube morphisms. -/
theorem connection_complement_not_zero :
    Cube.ofRaw (a := ⟨1⟩) (b := ⟨1⟩)
      (fun _ => .meet (.var 0) (.neg (.var 0))) ≠ Cube.zeroLine := by
  intro h
  have hc := Quotient.exact h
  have bad := Four.sound (fun _ => (true, false)) (hc 0)
  cases bad

end SquareKit.Cubical
