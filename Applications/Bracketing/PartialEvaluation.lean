import Applications.Bracketing.Basic

/-! Domain-sensitive evaluation of existing parenthesized trees. -/
namespace Bracketing

def Tree.eval (op : α → α → α) : Tree α → α
  | .leaf x => x
  | .fork l r => op (l.eval op) (r.eval op)

def Tree.Valid (domain : α → Prop) (op : α → α → α) : Tree α → Prop
  | .leaf x => domain x
  | .fork l r => l.Valid domain op ∧ r.Valid domain op ∧
      domain (op (l.eval op) (r.eval op))

theorem Tree.valid_eval {t : Tree α} {domain : α → Prop} {op : α → α → α} (h : t.Valid domain op) : domain (t.eval op) := by
  cases t with
  | leaf => exact h
  | fork => exact h.2.2

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf x => .leaf (f x)
  | .fork l r => .fork (l.map f) (r.map f)

/-- Only domain preservation and the local operation equation are used. -/
theorem Tree.preservation (f : α → β) (op : α → α → α) (op' : β → β → β)
    (D : α → Prop) (E : β → Prop) (hf : ∀ x, D x → E (f x))
    (hop : ∀ x, D x → ∀ y, D y → D (op x y) → f (op x y) = op' (f x) (f y))
    (t : Tree α) (ht : t.Valid D op) :
    (t.map f).eval op' = f (t.eval op) ∧ (t.map f).Valid E op' := by
  induction t with
  | leaf x => exact ⟨rfl, hf x ht⟩
  | fork l r ihl ihr =>
    obtain ⟨hel, hvl⟩ := ihl ht.1
    obtain ⟨her, hvr⟩ := ihr ht.2.1
    have he := hop _ (Tree.valid_eval ht.1) _ (Tree.valid_eval ht.2.1) ht.2.2
    refine ⟨?_, hvl, hvr, ?_⟩
    · simpa only [Tree.map, Tree.eval, hel, her] using he.symm
    · simpa only [Tree.eval, hel, her, ← he] using hf _ ht.2.2

end Bracketing
