import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Squares

/-! Ordinary value/observation pairs, with sequencing and additive observations.
No commutativity is required: observations are combined in execution order.
This is the additive pair form of writer composition, without a new syntax or
state backend. Resource bounds remain separate predicates. -/
namespace Resources
universe u v w x y
variable {α : Type u} {β : Type x} {γ : Type y} {C : Type v} {D : Type w}

abbrev Measured (α : Type u) (C : Type v) := α × C

def pure [Zero C] (a : α) : Measured α C := (a, 0)

def bind [Add C] (r : Measured α C) (f : α → Measured β C) : Measured β C :=
  let s := f r.1
  (s.1, r.2 + s.2)

def reweight (h : C → D) (r : Measured α C) : Measured α D := (r.1, h r.2)

@[simp] theorem bind_value [Add C] (r : Measured α C) (f : α → Measured β C) :
    (bind r f).1 = (f r.1).1 := rfl

@[simp] theorem reweight_value (h : C → D) (r : Measured α C) :
    (reweight h r).1 = r.1 := rfl

theorem bind_assoc [AddSemigroup C] (r : Measured α C)
    (f : α → Measured β C) (g : β → Measured γ C) :
    bind (bind r f) g = bind r (fun x => bind (f x) g) := by
  simp [bind, add_assoc]

theorem bind_pure [AddZeroClass C] (r : Measured α C) : bind r pure = r := by
  simp [bind, pure]

theorem pure_bind [AddZeroClass C] (a : α) (f : α → Measured β C) : bind (pure a) f = f a := by
  simp [bind, pure]

theorem bind_erases [Add C] (f : α → Measured β C) (g : β → Measured γ C)
    (f₀ : α → β) (g₀ : β → γ) (hf : ∀ x, (f x).1 = f₀ x)
    (hg : ∀ y, (g y).1 = g₀ y) (x : α) :
    (bind (f x) g).1 = g₀ (f₀ x) := by rw [bind_value, hg, hf]

theorem reweight_bind [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (r : Measured α C) (f : α → Measured β C) :
    reweight h (bind r f) = bind (reweight h r) (fun x => reweight h (f x)) := by
  simp [reweight, bind, map_add]

theorem reweight_bound [Preorder C] [Preorder D] (h : C → D) (hm : Monotone h)
    (r : Measured α C) (bound : C) (hb : r.2 ≤ bound) :
    (reweight h r).2 ≤ h bound := hm hb

/-- Package an existing measured function and its erasure proof directly. -/
def erasureSquare {α β C : Type u} (f : α → Measured β C) (g : α → β)
    (correct : ∀ x, (f x).1 = g x) :
    Squares.Square ⟨α, α, id⟩ ⟨Measured β C, β, Prod.fst⟩ where
  impl := f
  spec := g
  commutes := correct

/-- Output agreement imposes no equality on observations. -/
theorem same_value_different_cost :
    (((), 0) : Measured Unit Nat).1 = (((), 1) : Measured Unit Nat).1 ∧
    (((), 0) : Measured Unit Nat).2 ≠ (((), 1) : Measured Unit Nat).2 := by decide

end Resources
