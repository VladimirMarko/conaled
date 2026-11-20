import Applications.Trees.BasicObservations

/-!
# Two source joins with the same inorder observation

Both algorithms recurse on the facing children. `join` inspects that result
and promotes its root; `join0` keeps the original left root. These are distinct
tree-valued operators. Their label-set proofs below are structural and do not
depend on the separate inorder refinements.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

def join : BinaryTree α → BinaryTree α → BinaryTree α
  | .nil, r => r
  | l, .nil => l
  | .node a l m, .node b n r =>
      match join m n with
      | .nil => .node a l (.node b .nil r)
      | .node x p q => .node x (.node a l p) (.node b q r)

@[simp] theorem join_nil_left (r : BinaryTree α) : join .nil r = r := rfl

@[simp] theorem join_nil_right (l : BinaryTree α) : join l .nil = l := by
  cases l <;> rfl

theorem join_node_node (a b : α) (l m n r : BinaryTree α) :
    join (.node a l m) (.node b n r) =
      match join m n with
      | .nil => .node a l (.node b .nil r)
      | .node x p q => .node x (.node a l p) (.node b q r) := rfl

theorem inorder_join (l r : BinaryTree α) :
    inorder (join l r) = inorder l ++ inorder r := by
  induction l generalizing r with
  | nil => simp
  | node a l m _ ihm =>
      cases r with
      | nil => simp
      | node b n r =>
          have ih := ihm n
          cases h : join m n with
          | nil =>
              rw [h] at ih
              rw [join_node_node, h]
              simpa only [inorder_node, inorder_nil, List.nil_append,
                List.append_assoc, List.cons_append] using
                congrArg (fun xs => inorder l ++ a :: (xs ++ b :: inorder r)) ih
          | node x p q =>
              rw [h] at ih
              rw [join_node_node, h]
              simpa only [inorder_node, List.append_assoc, List.cons_append] using
                congrArg (fun xs => inorder l ++ a :: (xs ++ b :: inorder r)) ih

/-- Arbitrary raw labels, with no ordering or duplicate-freedom assumption. -/
theorem mem_setTree_join (l r : BinaryTree α) (z : α) :
    z ∈ setTree (join l r) ↔ z ∈ setTree l ∨ z ∈ setTree r := by
  induction l generalizing r with
  | nil => simp
  | node a l m _ ihm =>
      cases r with
      | nil => simp
      | node b n r =>
          have ih := ihm n
          cases h : join m n with
          | nil =>
              rw [h] at ih
              rw [join_node_node, h]
              simp only [setTree_node, setTree_nil, Set.mem_union,
                Set.mem_empty_iff_false, Set.mem_singleton_iff] at ih ⊢
              tauto
          | node x p q =>
              rw [h] at ih
              rw [join_node_node, h]
              simp only [setTree_node, Set.mem_union, Set.mem_singleton_iff] at ih ⊢
              tauto

theorem setTree_join (l r : BinaryTree α) :
    setTree (join l r) = setTree l ∪ setTree r := by
  ext z
  exact mem_setTree_join l r z

theorem forall_mem_join (P : α → Prop) (l r : BinaryTree α) :
    (∀ z ∈ setTree (join l r), P z) ↔
      (∀ z ∈ setTree l, P z) ∧ ∀ z ∈ setTree r, P z := by
  constructor
  · intro h
    exact ⟨fun z hz => h z ((mem_setTree_join l r z).mpr (Or.inl hz)),
      fun z hz => h z ((mem_setTree_join l r z).mpr (Or.inr hz))⟩
  · rintro ⟨hl, hr⟩ z hz
    rcases (mem_setTree_join l r z).mp hz with hz | hz
    · exact hl z hz
    · exact hr z hz

theorem numNodes_join (l r : BinaryTree α) :
    (join l r).numNodes = l.numNodes + r.numNodes := by
  rw [← inorder_length (join l r), inorder_join, List.length_append,
    inorder_length, inorder_length]

def join0 : BinaryTree α → BinaryTree α → BinaryTree α
  | .nil, r => r
  | l, .nil => l
  | .node a l m, .node b n r => .node a l (.node b (join0 m n) r)

@[simp] theorem join0_nil_left (r : BinaryTree α) : join0 .nil r = r := rfl

@[simp] theorem join0_nil_right (l : BinaryTree α) : join0 l .nil = l := by
  cases l <;> rfl

theorem join0_node_node (a b : α) (l m n r : BinaryTree α) :
    join0 (.node a l m) (.node b n r) = .node a l (.node b (join0 m n) r) := rfl

theorem inorder_join0 (l r : BinaryTree α) :
    inorder (join0 l r) = inorder l ++ inorder r := by
  induction l generalizing r with
  | nil => simp
  | node a l m _ ihm =>
      cases r with
      | nil => simp
      | node b n r =>
          rw [join0_node_node]
          simpa only [inorder_node, List.append_assoc, List.cons_append] using
            congrArg (fun xs => inorder l ++ a :: (xs ++ b :: inorder r)) (ihm n)

theorem mem_setTree_join0 (l r : BinaryTree α) (z : α) :
    z ∈ setTree (join0 l r) ↔ z ∈ setTree l ∨ z ∈ setTree r := by
  induction l generalizing r with
  | nil => simp
  | node a l m _ ihm =>
      cases r with
      | nil => simp
      | node b n r =>
          rw [join0_node_node]
          simp only [setTree_node, Set.mem_union, Set.mem_singleton_iff, ihm]
          tauto

theorem setTree_join0 (l r : BinaryTree α) :
    setTree (join0 l r) = setTree l ∪ setTree r := by
  ext z
  exact mem_setTree_join0 l r z

theorem forall_mem_join0 (P : α → Prop) (l r : BinaryTree α) :
    (∀ z ∈ setTree (join0 l r), P z) ↔
      (∀ z ∈ setTree l, P z) ∧ ∀ z ∈ setTree r, P z := by
  constructor
  · intro h
    exact ⟨fun z hz => h z ((mem_setTree_join0 l r z).mpr (Or.inl hz)),
      fun z hz => h z ((mem_setTree_join0 l r z).mpr (Or.inr hz))⟩
  · rintro ⟨hl, hr⟩ z hz
    rcases (mem_setTree_join0 l r z).mp hz with hz | hz
    · exact hl z hz
    · exact hr z hz

theorem numNodes_join0 (l r : BinaryTree α) :
    (join0 l r).numNodes = l.numNodes + r.numNodes := by
  rw [← inorder_length (join0 l r), inorder_join0, List.length_append,
    inorder_length, inorder_length]

end Trees
