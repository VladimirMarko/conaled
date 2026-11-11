import Applications.Resources.WholeListTrim
import Applications.Resources.Potential

/-! Tail-first pruning of whole-list predicates, through native measured steps. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.FoldedPrune
universe u v
variable {α : Type u}

/-- Independent recursive value contract; each stage uses longest-prefix Spec. -/
inductive Spec (p : List α → Bool) : List α → List α → Prop
  | nil : Spec p [] []
  | cons {x : α} {xs old out : List α} : Spec p xs old →
      WholeListTrim.Spec p (x :: old) out → Spec p (x :: xs) out

/-- Acceptance survives removing a head, with empty exhaustion admissible. -/
def TailClosed (p : List α → Bool) : Prop :=
  ∀ x xs, p (x :: xs) = true → WholeListTrim.Accept p xs

end Resources.FoldedPrune
