import Applications.Search.OrderedTree.Observations

/-! Every node triple, independently of the recursive ordering predicate.
Both child bounds quantify over entire subtrees. The characterization needs
only the supplied strict relation, with no transitivity or decidability. -/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u v
variable {α : Type u} {κ : Type v}

def nodes (t : BinaryTree α) : Set (α × BinaryTree α × BinaryTree α) :=
  fun p => Trees.Subtree (.node p.1 p.2.1 p.2.2) t

@[simp] theorem nodes_nil : nodes (.nil : BinaryTree α) = ∅ := by
  ext p
  change Trees.Subtree (.node p.1 p.2.1 p.2.2) .nil ↔ False
  simp

theorem nodes_node (a : α) (l r : BinaryTree α) :
    nodes (.node a l r) = {(a, l, r)} ∪ nodes l ∪ nodes r := by
  ext p
  rcases p with ⟨x, s, t⟩
  simp only [Set.mem_union, Set.mem_singleton_iff]
  change Trees.Subtree (.node x s t) (.node a l r) ↔
    ((x, s, t) = (a, l, r) ∨ Trees.Subtree (.node x s t) l) ∨
      Trees.Subtree (.node x s t) r
  simp only [Trees.subtree_node_iff, BinaryTree.node.injEq, Prod.mk.injEq, or_assoc]

def OrderedNodesBy [LT κ] (key : α → κ) (t : BinaryTree α) : Prop :=
  ∀ a l r, (a, l, r) ∈ nodes t →
    (∀ x ∈ Trees.setTree l, key x < key a) ∧
    ∀ x ∈ Trees.setTree r, key a < key x

theorem orderedBy_of_subtree [LT κ] {key : α → κ} {s t : BinaryTree α}
    (hst : Trees.Subtree s t) (ordered : OrderedBy key t) : OrderedBy key s := by
  induction hst with
  | refl => exact ordered
  | left _ _ ih => exact ih ordered.1
  | right _ _ ih => exact ih ordered.2.1

theorem orderedNodesBy_iff [LT κ] (key : α → κ) (t : BinaryTree α) :
    OrderedNodesBy key t ↔ OrderedBy key t := by
  constructor
  · intro h
    induction t with
    | nil => trivial
    | node a l r ihl ihr =>
        have rootBounds := h a l r (Trees.Subtree.refl _)
        exact ⟨ihl (fun x s u hx => h x s u (Trees.Subtree.left a hx)),
          ihr (fun x s u hx => h x s u (Trees.Subtree.right a hx)),
          (all_iff_mem_setTree _ _).mpr rootBounds.1,
          (all_iff_mem_setTree _ _).mpr rootBounds.2⟩
  · intro h a l r hn
    have ho := orderedBy_of_subtree hn h
    exact ⟨(all_iff_mem_setTree _ _).mp ho.2.2.1,
      (all_iff_mem_setTree _ _).mp ho.2.2.2⟩

def OrderedNodes [LT α] : BinaryTree α → Prop := OrderedNodesBy id

theorem orderedNodes_iff [LT α] (t : BinaryTree α) :
    OrderedNodes t ↔ Ordered t := orderedNodesBy_iff id t

end Search.OrderedTree
