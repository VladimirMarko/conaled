import Applications.Resources.ListExecution
import Mathlib.Data.List.Basic

/-! Longest acceptable prefix for a predicate on whole lists. Empty exhaustion
is admissible even when the predicate rejects empty. This differs from SuffixTrim. -/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.WholeListTrim

universe u v
variable {α : Type u}

def Accept (p : List α → Bool) (xs : List α) : Prop := xs = [] ∨ p xs = true

/-- Independent longest-prefix contract; no recursion, prices or closure premise. -/
def Spec (p : List α → Bool) (xs out : List α) : Prop :=
  out <+: xs ∧ Accept p out ∧
    ∀ ys, ys <+: xs → Accept p ys → ys.length ≤ out.length

/-- Finite ordinary-list prefix checks suffice to certify an independent answer. -/
theorem Spec.of_checks (p : List α → Bool) (xs out : List α)
    (hprefix : out <+: xs) (accepted : Accept p out)
    (maximal : ∀ i : Fin (xs.length + 1), Accept p (xs.take i.val) → i.val ≤ out.length) :
    Spec p xs out := by
  refine ⟨hprefix, accepted, ?_⟩
  intro ys hy ha
  have hlen := hy.length_le
  apply maximal ⟨ys.length, by omega⟩
  simpa only [← List.prefix_iff_eq_take.mp hy] using ha

end Resources.WholeListTrim
