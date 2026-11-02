import Applications.Trees.Observations
import Mathlib.Data.List.Sort

/-! Recursive subtree bounds and their ordered inorder observation on the
existing node-labelled tree. Relation laws, strict key order and payload
mapping remain separate contracts. Source and statement assessment:
`docs/research/fdsa-tree-order.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- Every left label precedes the root, every right label follows it,
and the same condition holds recursively in both children. -/
def Ordered (R : α → α → Prop) : BinaryTree α → Prop
  | .nil => True
  | .node a l r =>
      Ordered R l ∧ Ordered R r ∧
        (∀ x ∈ inorder l, R x a) ∧ (∀ y ∈ inorder r, R a y)

@[simp] theorem ordered_nil (R : α → α → Prop) :
    Ordered R (.nil : BinaryTree α) := trivial

@[simp] theorem ordered_node (R : α → α → Prop) (a : α)
    (l r : BinaryTree α) :
    Ordered R (.node a l r) ↔
      Ordered R l ∧ Ordered R r ∧
        (∀ x ∈ inorder l, R x a) ∧ (∀ y ∈ inorder r, R a y) := Iff.rfl

/-- The all-pairs observation supplies the recursive bounds for any relation. -/
theorem ordered_of_pairwise_inorder (R : α → α → Prop) (t : BinaryTree α)
    (h : (inorder t).Pairwise R) : Ordered R t := by
  revert h
  induction t with
  | nil => exact fun _ => ordered_nil R
  | node a l r ihl ihr =>
      intro h
      rw [inorder_node] at h
      rcases List.pairwise_append.mp h with ⟨hl, har, hlr⟩
      rcases List.pairwise_cons.mp har with ⟨ha, hr⟩
      exact ⟨ihl hl, ihr hr, fun x hx => hlr x hx a List.mem_cons_self, ha⟩

/-- Transitivity supplies the cross-subtree comparisons through the root. -/
theorem pairwise_inorder_of_ordered (R : α → α → Prop) (hR : Transitive R)
    (t : BinaryTree α) (h : Ordered R t) : (inorder t).Pairwise R := by
  revert h
  induction t with
  | nil => exact fun _ => List.Pairwise.nil
  | node a l r ihl ihr =>
      rintro ⟨hl, hr, hla, har⟩
      rw [inorder_node, List.pairwise_append, List.pairwise_cons]
      refine ⟨ihl hl, ⟨har, ihr hr⟩, ?_⟩
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hla x hx
      · exact hR (hla x hx) (har y hy)

theorem ordered_iff_pairwise_inorder (R : α → α → Prop) (hR : Transitive R)
    (t : BinaryTree α) : Ordered R t ↔ (inorder t).Pairwise R :=
  ⟨pairwise_inorder_of_ordered R hR t, ordered_of_pairwise_inorder R t⟩

/-- Exact inorder equality transports and reflects a transitive invariant. -/
theorem ordered_congr_inorder (R : α → α → Prop) (hR : Transitive R)
    (t s : BinaryTree α) (h : inorder t = inorder s) : Ordered R t ↔ Ordered R s := by
  rw [ordered_iff_pairwise_inorder R hR t, ordered_iff_pairwise_inorder R hR s, h]

/-- Relation weakening preserves the structural invariant without relation laws. -/
theorem ordered_mono (R S : α → α → Prop) (hRS : ∀ a b, R a b → S a b)
    (t : BinaryTree α) (h : Ordered R t) : Ordered S t := by
  revert h
  induction t with
  | nil => exact fun _ => ordered_nil S
  | node a l r ihl ihr =>
      rintro ⟨hl, hr, hla, har⟩
      exact ⟨ihl hl, ihr hr, fun x hx => hRS x a (hla x hx),
        fun y hy => hRS a y (har y hy)⟩

/-- Pull back the relation along any label map, without injectivity or transitivity. -/
theorem ordered_map_iff (S : β → β → Prop) (f : α → β) (t : BinaryTree α) :
    Ordered S (t.map f) ↔ Ordered (fun a b => S (f a) (f b)) t := by
  induction t with
  | nil => exact Iff.rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, ordered_node, inorder_map, List.forall_mem_map, ihl, ihr]

/-- Forward transport uses relation preservation; it does not assert reflection. -/
theorem ordered_map (R : α → α → Prop) (S : β → β → Prop) (f : α → β)
    (hRS : ∀ a b, R a b → S (f a) (f b)) (t : BinaryTree α)
    (h : Ordered R t) : Ordered S (t.map f) :=
  (ordered_map_iff S f t).2 (ordered_mono R _ hRS t h)

/-- Key-preserving payload maps retain the exact pulled-back relation.
The payload map and key need not be globally injective. -/
theorem ordered_map_key_iff [LT κ] (key : α → κ) (key' : β → κ) (f : α → β)
    (hf : ∀ a, key' (f a) = key a) (t : BinaryTree α) :
    Ordered (fun a b => key' a < key' b) (t.map f) ↔
      Ordered (fun a b => key a < key b) t := by
  simpa only [hf] using ordered_map_iff (fun a b => key' a < key' b) f t

/-- Strict key order needs only a preorder on keys and no order on payloads. -/
theorem ordered_key_iff_pairwise [Preorder κ] (key : α → κ) (t : BinaryTree α) :
    Ordered (fun a b => key a < key b) t ↔
      ((inorder t).map key).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact ordered_iff_pairwise_inorder _ (fun _ _ _ hab hbc => lt_trans hab hbc) t

theorem ordered_key_iff_sortedLT [Preorder κ] (key : α → κ) (t : BinaryTree α) :
    Ordered (fun a b => key a < key b) t ↔ ((inorder t).map key).SortedLT :=
  (ordered_key_iff_pairwise key t).trans List.sortedLT_iff_pairwise.symm

/-- Distinctness concerns the mapped keys, not merely distinct payload records. -/
theorem ordered_key_nodup [Preorder κ] (key : α → κ) (t : BinaryTree α)
    (h : Ordered (fun a b => key a < key b) t) : ((inorder t).map key).Nodup :=
  ((ordered_key_iff_sortedLT key t).1 h).nodup

/-- The weak-order converse requires antisymmetry on keys. -/
theorem ordered_key_iff_nodup_sortedLE [PartialOrder κ]
    (key : α → κ) (t : BinaryTree α) :
    Ordered (fun a b => key a < key b) t ↔
      ((inorder t).map key).Nodup ∧ ((inorder t).map key).SortedLE :=
  (ordered_key_iff_sortedLT key t).trans List.sortedLT_iff_nodup_and_sortedLE

end Trees
