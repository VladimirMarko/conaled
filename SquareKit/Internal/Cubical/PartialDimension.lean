import SquareKit.Internal.Cubical.Dimensions
import Mathlib.Data.Fintype.Option

/-! Partial assignments used to construct the finite cubical face lattice.
The unspecified value is not a Boolean endpoint. -/
namespace SquareKit.Cubical.PartialDimension
abbrev Carrier := Option Bool

def neg : Carrier → Carrier
  | none => none
  | some b => some (!b)
def meet : Carrier → Carrier → Carrier
  | some false, _ => some false
  | _, some false => some false
  | some true, x => x
  | x, some true => x
  | none, none => none
def join : Carrier → Carrier → Carrier
  | some true, _ => some true
  | _, some true => some true
  | some false, x => x
  | x, some false => x
  | none, none => none

def eval (ρ : α → Carrier) : Expr α → Carrier
  | .zero => (some false)
  | .one => (some true)
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
  | meet_one a => exact (by decide : ∀ x, meet x (some true) = x) _
  | meet_zero a => exact (by decide : ∀ x, meet x (some false) = (some false)) _
  | join_comm a b => exact (by decide : ∀ x y, join x y = join y x) _ _
  | join_assoc a b c => exact (by decide : ∀ x y z, join (join x y) z = join x (join y z)) _ _ _
  | join_idem a => exact (by decide : ∀ x, join x x = x) _
  | join_zero a => exact (by decide : ∀ x, join x (some false) = x) _
  | join_one a => exact (by decide : ∀ x, join x (some true) = (some true)) _
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

/-- Information refinement: an unspecified coordinate can become an endpoint. -/
def Refines (a b : Carrier) : Prop := a = none ∨ a = b
instance (a b : Carrier) : Decidable (Refines a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem refines_refl (a : Carrier) : Refines a a := Or.inr rfl

theorem neg_refines : ∀ a b, Refines a b → Refines (neg a) (neg b) := by decide

theorem meet_refines : ∀ a a' b b', Refines a a' → Refines b b' → Refines (meet a b) (meet a' b') := by decide

theorem join_refines : ∀ a a' b b', Refines a a' → Refines b b' → Refines (join a b) (join a' b') := by decide

theorem eval_refines (ρ τ : α → Carrier) (h : ∀ i, Refines (ρ i) (τ i)) (e : Expr α) :
    Refines (eval ρ e) (eval τ e) := by
  induction e with
  | zero => exact refines_refl _
  | one => exact refines_refl _
  | var i => exact h i
  | neg e ih => exact neg_refines _ _ ih
  | meet e f ih jh => exact meet_refines _ _ _ _ ih jh
  | join e f ih jh => exact join_refines _ _ _ _ ih jh

end SquareKit.Cubical.PartialDimension
