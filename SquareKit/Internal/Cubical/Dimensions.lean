import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fin.Basic

/-!
# De Morgan dimension substitutions

The cube base for the construction in issue #321. Dimensions are formal terms
modulo the bounded distributive De Morgan equations, not Boolean functions.
This module constructs the cube category. It does not yet construct fibrancy,
dependent types, or a cubical type-theory interpretation.
-/

namespace SquareKit.Cubical

/-- Raw dimension expressions over names `α`. -/
inductive Expr (α : Type) where
  | zero | one
  | var (name : α)
  | neg (a : Expr α)
  | meet (a b : Expr α)
  | join (a b : Expr α)
  deriving DecidableEq

namespace Expr

/-- Simultaneous dimension substitution. -/
def subst (σ : α → Expr β) : Expr α → Expr β
  | zero => zero
  | one => one
  | var a => σ a
  | neg a => neg (subst σ a)
  | meet a b => meet (subst σ a) (subst σ b)
  | join a b => join (subst σ a) (subst σ b)

@[simp] theorem subst_var (a : Expr α) : subst var a = a := by
  induction a <;> simp_all [subst]

@[simp] theorem subst_subst (σ : α → Expr β) (τ : β → Expr γ) (a : Expr α) :
    subst τ (subst σ a) = subst (fun x => subst τ (σ x)) a := by
  induction a <;> simp_all [subst]

/-- The equational congruence of bounded distributive De Morgan algebras.
Excluded middle and disjoint complements are deliberately absent. -/
inductive Conv : Expr α → Expr α → Prop where
  | refl (a) : Conv a a
  | symm : Conv a b → Conv b a
  | trans : Conv a b → Conv b c → Conv a c
  | neg : Conv a b → Conv (.neg a) (.neg b)
  | meet : Conv a a' → Conv b b' → Conv (.meet a b) (.meet a' b')
  | join : Conv a a' → Conv b b' → Conv (.join a b) (.join a' b')
  | meet_comm (a b) : Conv (.meet a b) (.meet b a)
  | meet_assoc (a b c) : Conv (.meet (.meet a b) c) (.meet a (.meet b c))
  | meet_idem (a) : Conv (.meet a a) a
  | meet_one (a) : Conv (.meet a .one) a
  | meet_zero (a) : Conv (.meet a .zero) .zero
  | join_comm (a b) : Conv (.join a b) (.join b a)
  | join_assoc (a b c) : Conv (.join (.join a b) c) (.join a (.join b c))
  | join_idem (a) : Conv (.join a a) a
  | join_zero (a) : Conv (.join a .zero) a
  | join_one (a) : Conv (.join a .one) .one
  | absorb_meet (a b) : Conv (.meet a (.join a b)) a
  | absorb_join (a b) : Conv (.join a (.meet a b)) a
  | distrib_meet (a b c) : Conv (.meet a (.join b c)) (.join (.meet a b) (.meet a c))
  | distrib_join (a b c) : Conv (.join a (.meet b c)) (.meet (.join a b) (.join a c))
  | neg_neg (a) : Conv (.neg (.neg a)) a
  | neg_zero : Conv (.neg .zero) .one
  | neg_one : Conv (.neg .one) .zero
  | neg_meet (a b) : Conv (.neg (.meet a b)) (.join (.neg a) (.neg b))
  | neg_join (a b) : Conv (.neg (.join a b)) (.meet (.neg a) (.neg b))

theorem Conv.subst (σ : α → Expr β) (h : Conv a b) :
    Conv (Expr.subst σ a) (Expr.subst σ b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'
  | neg _ ih => exact .neg ih
  | meet _ _ ih ih' => exact .meet ih ih'
  | join _ _ ih ih' => exact .join ih ih'
  | meet_comm => exact .meet_comm _ _
  | meet_assoc => exact .meet_assoc _ _ _
  | meet_idem => exact .meet_idem _
  | meet_one => exact .meet_one _
  | meet_zero => exact .meet_zero _
  | join_comm => exact .join_comm _ _
  | join_assoc => exact .join_assoc _ _ _
  | join_idem => exact .join_idem _
  | join_zero => exact .join_zero _
  | join_one => exact .join_one _
  | absorb_meet => exact .absorb_meet _ _
  | absorb_join => exact .absorb_join _ _
  | distrib_meet => exact .distrib_meet _ _ _
  | distrib_join => exact .distrib_join _ _ _
  | neg_neg => exact .neg_neg _
  | neg_zero => exact .neg_zero
  | neg_one => exact .neg_one
  | neg_meet => exact .neg_meet _ _
  | neg_join => exact .neg_join _ _

theorem subst_congr (σ τ : α → Expr β) (h : ∀ x, Conv (σ x) (τ x)) (a : Expr α) :
    Conv (subst σ a) (subst τ a) := by
  induction a with
  | zero => exact .refl _
  | one => exact .refl _
  | var x => exact h x
  | neg a ih => exact .neg ih
  | meet a b ih ih' => exact .meet ih ih'
  | join a b ih ih' => exact .join ih ih'

end Expr

/-- Finite dimension contexts, with substitutions pointing in geometric order. -/
structure Cube where
  dimension : ℕ
  deriving DecidableEq

namespace Cube

abbrev Raw (a b : Cube) := Fin b.dimension → Expr (Fin a.dimension)

def rawSetoid (a b : Cube) : Setoid (Raw a b) where
  r σ τ := ∀ i, Expr.Conv (σ i) (τ i)
  iseqv := ⟨fun _ _ => .refl _, fun h i => .symm (h i), fun h k i => .trans (h i) (k i)⟩

/-- Actual equivalence classes of dimension substitutions. -/
def Hom (a b : Cube) := Quotient (rawSetoid a b)

def ofRaw (σ : Raw a b) : Hom a b := Quotient.mk _ σ

def identity (a : Cube) : Hom a a := ofRaw Expr.var

def comp (σ : Hom a b) (τ : Hom b c) : Hom a c :=
  Quotient.map₂ (fun σ τ i => Expr.subst σ (τ i))
    (by
      intro σ σ' h τ τ' k i
      exact (Expr.Conv.subst σ (k i)).trans (Expr.subst_congr σ σ' h (τ' i))) σ τ

@[simp] theorem comp_ofRaw (σ : Raw a b) (τ : Raw b c) :
    comp (ofRaw σ) (ofRaw τ) = ofRaw (fun i => Expr.subst σ (τ i)) := rfl

instance : CategoryTheory.Category Cube where
  Hom := Hom
  id := identity
  comp := comp
  id_comp := by
    intro a b σ
    refine Quotient.inductionOn σ ?_
    intro σ
    apply Quotient.sound
    intro i
    simpa [Expr.subst_var] using Expr.Conv.refl (σ i)
  comp_id := by
    intro a b σ
    refine Quotient.inductionOn σ ?_
    intro σ
    rfl
  assoc := by
    intro a b c d σ τ υ
    refine Quotient.inductionOn₃ σ τ υ ?_
    intro σ τ υ
    apply Quotient.sound
    intro i
    change Expr.Conv (Expr.subst (fun j => Expr.subst σ (τ j)) (υ i))
      (Expr.subst σ (Expr.subst τ (υ i)))
    rw [Expr.subst_subst]
    exact .refl _

/-- The connection `(i,j) ↦ i ∧ j`. -/
def connection : Hom ⟨2⟩ ⟨1⟩ := ofRaw (fun _ => .meet (.var 0) (.var 1))

/-- A face fixes the last coordinate and retains the first. -/
def face (endpoint : Bool) : Hom ⟨1⟩ ⟨2⟩ :=
  ofRaw (fun i => if i = 0 then .var 0 else if endpoint then .one else .zero)

def zeroLine : Hom ⟨1⟩ ⟨1⟩ := ofRaw (fun _ => .zero)

/-- The first boundary equation in the source cube contraction. -/
theorem face_zero_connection : comp (face false) connection = zeroLine := by
  apply Quotient.sound
  intro i
  exact .meet_zero (.var 0)

/-- The second boundary equation retains the entire variable line. -/
theorem face_one_connection : comp (face true) connection = identity ⟨1⟩ := by
  apply Quotient.sound
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact .meet_one (.var 0)

/-- Reversal is a dimension substitution, rather than Boolean case analysis. -/
def reversal : Hom ⟨1⟩ ⟨1⟩ := ofRaw (fun _ => .neg (.var 0))

theorem reversal_twice : comp reversal reversal = identity ⟨1⟩ := by
  apply Quotient.sound
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact .neg_neg (.var 0)

end Cube
end SquareKit.Cubical
