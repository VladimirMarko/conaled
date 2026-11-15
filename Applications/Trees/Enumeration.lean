import Applications.Trees.Observations
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic

/-! Enumerate every finite binary tree with a prescribed inorder list.
Inserting the next first label at every position on the left spine is executable
and preserves the label order. Deleting the first node recovers the predecessor,
so distinctness of the output does not require distinctness of the labels.
No runtime complexity claim is made for this enumeration.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

/-- Every way to prepend a label to the inorder traversal of a fixed tree. -/
def insertFirst (x : α) : BinaryTree α → List (BinaryTree α)
  | .nil => [.node x .nil .nil]
  | .node a l r =>
      .node x .nil (.node a l r) ::
        (insertFirst x l).map (fun l' => .node a l' r)

@[simp] theorem insertFirst_nil (x : α) :
    insertFirst x .nil = [.node x .nil .nil] := rfl

@[simp] theorem insertFirst_node (x a : α) (l r : BinaryTree α) :
    insertFirst x (.node a l r) = .node x .nil (.node a l r) ::
      (insertFirst x l).map (fun l' => .node a l' r) := rfl

/-- Delete the first node in inorder, replacing it by its right subtree. -/
def removeFirst : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node _ .nil r => r
  | .node a (.node b ll lr) r =>
      .node a (removeFirst (.node b ll lr)) r

theorem removeFirst_node_of_ne_nil (a : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
    removeFirst (.node a l r) = .node a (removeFirst l) r := by
  cases l <;> simp_all [removeFirst]

@[simp] theorem nil_not_mem_insertFirst (x : α) (t : BinaryTree α) :
    (.nil : BinaryTree α) ∉ insertFirst x t := by
  cases t <;> simp [insertFirst]

theorem inorder_of_mem_insertFirst (x : α) {s t : BinaryTree α}
    (ht : t ∈ insertFirst x s) : inorder t = x :: inorder s := by
  induction s generalizing t with
  | nil =>
      simp only [insertFirst, List.mem_singleton] at ht
      subst t
      rfl
  | node a l r ihl _ =>
      simp only [insertFirst, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨l', hl', rfl⟩
      · rfl
      · simp only [inorder_node, ihl (t := l') hl', List.cons_append]

/-- The deletion inverse separates outputs from different predecessor trees. -/
theorem removeFirst_of_mem_insertFirst (x : α) {s t : BinaryTree α}
    (ht : t ∈ insertFirst x s) : removeFirst t = s := by
  induction s generalizing t with
  | nil =>
      simp only [insertFirst, List.mem_singleton] at ht
      subst t
      rfl
  | node a l r ihl _ =>
      simp only [insertFirst, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨l', hl', rfl⟩
      · rfl
      · have hne : l' ≠ .nil := by
          intro h
          subst l'
          exact nil_not_mem_insertFirst x l hl'
        rw [removeFirst_node_of_ne_nil a l' r hne, ihl (t := l') hl']

theorem nodup_insertFirst (x : α) (t : BinaryTree α) :
    (insertFirst x t).Nodup := by
  induction t with
  | nil => simp [insertFirst]
  | node a l r ihl _ =>
      rw [insertFirst_node, List.nodup_cons]
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨l', hl', heq⟩
        have hnil : l' = .nil := congrArg BinaryTree.left heq
        subst l'
        exact nil_not_mem_insertFirst x l hl'
      · exact List.Nodup.map (fun s t h => congrArg BinaryTree.left h) ihl

/-- Every nonempty inorder traversal can be obtained by one first insertion. -/
theorem exists_insertFirst_of_inorder_cons (x : α) (xs : List α) (t : BinaryTree α)
    (ht : inorder t = x :: xs) :
    ∃ s, inorder s = xs ∧ t ∈ insertFirst x s := by
  induction t generalizing x xs with
  | nil => simp at ht
  | node a l r ihl _ =>
      cases l with
      | nil =>
          rw [inorder_node, inorder_nil, List.nil_append] at ht
          simp only [List.cons.injEq] at ht
          rcases ht with ⟨hroot, hxs⟩
          subst a
          refine ⟨r, hxs, ?_⟩
          cases r <;> simp [insertFirst]
      | node b ll lr =>
          have hn : inorder (.node b ll lr) ≠ [] := by simp
          obtain ⟨y, ys, hi⟩ := List.exists_cons_of_ne_nil hn
          rw [inorder_node, hi] at ht
          simp only [List.cons_append, List.cons.injEq] at ht
          rcases ht with ⟨hroot, hxs⟩
          subst y
          obtain ⟨s, hs, hmem⟩ := ihl x ys hi
          refine ⟨.node a s r, ?_, ?_⟩
          · simpa only [inorder_node, hs] using hxs
          · simp only [insertFirst_node, List.mem_cons, List.mem_map]
            exact Or.inr ⟨.node b ll lr, hmem, rfl⟩

theorem insertFirst_flatMap_nodup (x : α) (ts : List (BinaryTree α))
    (hts : ts.Nodup) : (ts.flatMap (insertFirst x)).Nodup := by
  revert hts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
      intro hts
      rcases List.nodup_cons.mp hts with ⟨ht, htail⟩
      rw [List.flatMap_cons]
      apply List.Nodup.append (nodup_insertFirst x t) (ih htail)
      apply List.disjoint_left.mpr
      intro s hs hs'
      rcases List.mem_flatMap.mp hs' with ⟨u, hu, hsu⟩
      have heq : t = u := (removeFirst_of_mem_insertFirst x hs).symm.trans
        (removeFirst_of_mem_insertFirst x hsu)
      exact ht (heq.symm ▸ hu)

/-- Enumerate all ordered tree shapes labelled by the prescribed inorder list. -/
def enumTree : List α → List (BinaryTree α)
  | [] => [.nil]
  | x :: xs => (enumTree xs).flatMap (insertFirst x)

@[simp] theorem enumTree_nil : enumTree ([] : List α) = [.nil] := rfl

@[simp] theorem enumTree_cons (x : α) (xs : List α) :
    enumTree (x :: xs) = (enumTree xs).flatMap (insertFirst x) := rfl

/-- Exact soundness and completeness, with order and repetitions preserved. -/
theorem mem_enumTree_iff (xs : List α) (t : BinaryTree α) :
    t ∈ enumTree xs ↔ inorder t = xs := by
  induction xs generalizing t with
  | nil => cases t <;> simp [enumTree]
  | cons x xs ih =>
      rw [enumTree_cons, List.mem_flatMap]
      constructor
      · rintro ⟨s, hs, ht⟩
        exact (inorder_of_mem_insertFirst x ht).trans
          (congrArg (List.cons x) ((ih s).mp hs))
      · intro ht
        obtain ⟨s, hs, hmem⟩ := exists_insertFirst_of_inorder_cons x xs t ht
        exact ⟨s, (ih s).mpr hs, hmem⟩

theorem set_enumTree (xs : List α) :
    {t | t ∈ enumTree xs} = {t : BinaryTree α | inorder t = xs} := by
  ext t
  exact mem_enumTree_iff xs t

/-- Repeated input labels do not cause any tree to be enumerated twice. -/
theorem enumTree_nodup (xs : List α) : (enumTree xs).Nodup := by
  induction xs with
  | nil => simp [enumTree]
  | cons x xs ih => exact insertFirst_flatMap_nodup x (enumTree xs) ih

end Trees
