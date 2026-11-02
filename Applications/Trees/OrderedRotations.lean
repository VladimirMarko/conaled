import Applications.Trees.Ordered
import Applications.Trees.CachedRotations

/-! Ordering consequences of the existing root-rotation observations.
Successful ordinary rotations preserve and reflect a transitive structural
invariant. Erased payload order remains separate from cache validity and
equality of cached summaries. Source and statement assessment:
`docs/research/fdsa-tree-order.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v
variable {α : Type u} {β : Type v}

/-- The conclusion concerns the actual successful result; failure remains `none`. -/
theorem ordered_rotateLeft?_iff (R : α → α → Prop) (hR : Transitive R)
    (t t' : BinaryTree α) (h : rotateLeft? t = some t') :
    Ordered R t' ↔ Ordered R t :=
  ordered_congr_inorder R hR t' t (inorder_of_rotateLeft? t t' h)

/-- The right-rotation adapter retains the same explicit success and relation laws. -/
theorem ordered_rotateRight?_iff (R : α → α → Prop) (hR : Transitive R)
    (t t' : BinaryTree α) (h : rotateRight? t = some t') :
    Ordered R t' ↔ Ordered R t :=
  ordered_congr_inorder R hR t' t (inorder_of_rotateRight? t t' h)

namespace Cached

/-- Rebuilt annotations need not agree or be valid for erased payload order to agree. -/
theorem ordered_erase_rebuildLeft_iff_rebuildRight
    (R : α → α → Prop) (hR : Transitive R)
    (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Ordered R (erase (rebuildLeft empty combine A x B y C)) ↔
      Ordered R (erase (rebuildRight empty combine A x B y C)) :=
  Trees.ordered_congr_inorder R hR _ _
    (inorder_erase_rebuildLeft_eq_rebuildRight empty combine A x B y C)

end Cached
end Trees
