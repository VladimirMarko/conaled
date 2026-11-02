import Applications.Resources.Measured

/-! Compositional equations for the explicit call-count model used by FDSA.
These are laws of measured values, not a source-language cost translator or a
claim about Lean's runtime. Primitive operations add no observation; a recursive
function entry adds one. Provenance: `docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.CallCount
universe u v w x
variable {α : Type u} {β : Type v} {γ : Type w} {C : Type x}

/-- Charge one recursive entry after evaluating its body in the source model. -/
def tick (r : Measured α Nat) : Measured α Nat := (r.1, r.2 + 1)

@[simp] theorem tick_value (r : Measured α Nat) : (tick r).1 = r.1 := rfl

@[simp] theorem tick_cost (r : Measured α Nat) : (tick r).2 = r.2 + 1 := rfl

/-- Zero-cost variables and primitives preserve the argument's observation. -/
theorem primitive_rule [AddZeroClass C] (f : α → β) (r : Measured α C) :
    bind r (fun a => pure (f a)) = (f r.1, r.2) := by
  simp [bind, pure]

/-- The body is evaluated at the value produced by the bound expression. -/
theorem let_rule [Add C] (r : Measured α C) (body : α → Measured β C) :
    bind r body = ((body r.1).1, r.2 + (body r.1).2) := rfl

/-- Argument evaluations precede the function's own measured computation.
Further arguments are handled by the same bind law and `Resources.bind_assoc`.
-/
theorem arguments_rule [Add C] (r : Measured α C) (s : Measured β C)
    (f : α → β → Measured γ C) :
    bind r (fun a => bind s (f a)) =
      ((f r.1 s.1).1, r.2 + (s.2 + (f r.1 s.1).2)) := rfl

/-- Only the selected branch contributes to the observation. -/
theorem if_rule [Add C] (b : Measured Bool C)
    (yes no : Unit → Measured α C) :
    bind b (fun v => if v then yes () else no ()) =
      (if b.1 then ((yes ()).1, b.2 + (yes ()).2)
       else ((no ()).1, b.2 + (no ()).2)) := by
  cases b with
  | mk value cost => cases value <;> rfl

/-- Pattern matching on a sum evaluates the scrutinee and the selected arm. -/
theorem case_rule [Add C] (r : Measured (α ⊕ β) C)
    (left : α → Measured γ C) (right : β → Measured γ C) :
    bind r (Sum.elim left right) =
      match r.1 with
      | .inl a => ((left a).1, r.2 + (left a).2)
      | .inr b => ((right b).1, r.2 + (right b).2) := by
  cases r with
  | mk value cost => cases value <;> rfl

end Resources.CallCount
