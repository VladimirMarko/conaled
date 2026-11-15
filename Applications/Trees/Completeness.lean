import Applications.Trees.Shape

/-! One executable completeness/height summary on the canonical tree fold.
Only natural heights are compared. The structural Complete predicate and
BinaryTree.height remain independent specifications of its two projections.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Completeness
universe u
variable {α : Type u}

def empty : Bool × Nat := (true, 0)

def combine (left : Bool × Nat) (_label : α) (right : Bool × Nat) : Bool × Nat :=
  ((left.1 && right.1) && (left.2 == right.2), max left.2 right.2 + 1)

def summary (t : BinaryTree α) : Bool × Nat := Trees.fold empty combine t

@[simp] theorem summary_nil : summary (.nil : BinaryTree α) = empty := rfl

@[simp] theorem summary_node (a : α) (l r : BinaryTree α) :
    summary (.node a l r) = combine (summary l) a (summary r) := rfl

/-- The height projection is a fusion into the existing height algebra. -/
theorem summary_height (t : BinaryTree α) : (summary t).2 = t.height := by
  calc
    (summary t).2 = Trees.fold 0 (fun l (_ : α) r => max l r + 1) t :=
      Trees.fold_fusion empty combine 0 (fun l (_ : α) r => max l r + 1)
        Prod.snd rfl (fun _ _ _ => rfl) t
    _ = t.height := Trees.fold_height t

/-- The flag reflects the existing independent perfect-tree predicate. -/
theorem summary_complete (t : BinaryTree α) : (summary t).1 = true ↔ Trees.Complete t := by
  induction t with
  | nil => simp [empty]
  | node a l r ihl ihr =>
      simp only [summary_node, combine, Bool.and_eq_true, beq_iff_eq,
        summary_height, ihl, ihr, Trees.complete_node]
      constructor
      · rintro ⟨⟨hl, hr⟩, heq⟩
        exact ⟨heq, hl, hr⟩
      · rintro ⟨heq, hl, hr⟩
        exact ⟨⟨hl, hr⟩, heq⟩

/-- A projection of the shared fold, not a second recursive checker. -/
def check (t : BinaryTree α) : Bool := (summary t).1

theorem check_correct (t : BinaryTree α) : check t = true ↔ Trees.Complete t :=
  summary_complete t

end Trees.Completeness
