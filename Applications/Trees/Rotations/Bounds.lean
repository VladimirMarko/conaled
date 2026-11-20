import Applications.Trees.Rotations.Normalize
import Applications.Trees.Enumeration
import Applications.Trees.TraversalWork

/-!
# Exact recovery, connection and optimal right-only listification

An arbitrary legal right step increases the whole right spine by at most one;
it need not increase it at all. Generated steps attain the resulting lower
bound. The two-phase connection of equal-inorder trees is a different result:
its length bound is not a claim that it is a shortest mixed-direction route.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
open Search.SharedTree (Branch)
universe u
variable {α : Type u}

/-- The unchanged left branch can hide a rotation from the whole right spine. -/
theorem applyAt?_rightLength_bounds (p : List Branch) {s t : BinaryTree α}
    (h : applyAt? rotateRight? p s = some t) :
    rightLength s ≤ rightLength t ∧ rightLength t ≤ rightLength s + 1 := by
  induction p generalizing s t with
  | nil =>
      have hr := rotateRight?_rightLength h
      omega
  | cons d p ih =>
      cases s with
      | nil => simp at h
      | node a l r =>
          cases d with
          | left =>
              cases hs : applyAt? rotateRight? p l with
              | none => simp [hs] at h
              | some l' =>
                  simp only [applyAt?_left, hs, Option.map_some, Option.some.injEq] at h
                  subst t
                  simp only [rightLength_node]
                  omega
          | right =>
              cases hs : applyAt? rotateRight? p r with
              | none => simp [hs] at h
              | some r' =>
                  simp only [applyAt?_right, hs, Option.map_some, Option.some.injEq] at h
                  subst t
                  have hr := ih hs
                  simp only [rightLength_node]
                  omega

theorem applyAts?_rightLength_le (ps : List (List Branch)) {s t : BinaryTree α}
    (h : applyAts? rotateRight? ps s = some t) :
    rightLength t ≤ rightLength s + ps.length := by
  induction ps generalizing s t with
  | nil => cases h; omega
  | cons p ps ih =>
      cases hs : applyAt? rotateRight? p s with
      | none => simp [hs] at h
      | some s' =>
          simp only [applyAts?_cons, hs, Option.bind_some] at h
          have first := (applyAt?_rightLength_bounds p hs).2
          have rest := ih h
          simp only [List.length_cons]
          omega

/-- Every successful right-only listifying schedule pays at least this amount. -/
theorem deficit_le_length {ps : List (List Branch)} {s t : BinaryTree α}
    (run : applyAts? rotateRight? ps s = some t) (form : IsList t) :
    s.numNodes - rightLength s ≤ ps.length := by
  have bound := applyAts?_rightLength_le ps run
  have size := numNodes_eq_of_inorder_eq
    (applyAts?_inorder rotateRight? rotateRight?_inorder ps run)
  have spine := rightLength_eq_numNodes form
  omega

theorem rightPositions_optimal {ps : List (List Branch)} {s t : BinaryTree α}
    (run : applyAts? rotateRight? ps s = some t) (form : IsList t) :
    (rightPositions s).length ≤ ps.length := by
  rw [rightPositions_length]
  exact deficit_le_length run form

theorem countRots_le_pred (t : BinaryTree α) : countRots t ≤ t.numNodes - 1 := by
  rw [countRots_eq_deficit]
  cases t with
  | nil => rfl
  | node a l r =>
      simp only [rightLength_node, BinaryTree.numNodes]
      omega

theorem rightPositions_length_le_pred (t : BinaryTree α) :
    (rightPositions t).length ≤ t.numNodes - 1 := by
  rw [← countRots_eq_length]
  exact countRots_le_pred t

theorem countRots_eq_pred {t : BinaryTree α} (h : rightLength t = 1) :
    countRots t = t.numNodes - 1 := by
  rw [countRots_eq_deficit, h]

/-- List form retains the complete ordered label sequence, including duplicates. -/
theorem eq_of_isList_of_inorder_eq {s t : BinaryTree α}
    (hs : IsList s) (ht : IsList t) (same : inorder s = inorder t) : s = t := by
  induction s generalizing t with
  | nil =>
      cases t with
      | nil => rfl
      | node a l r =>
          rcases ht with ⟨rfl, _⟩
          simp only [inorder_nil, inorder_node, List.nil_append] at same
          cases same
  | node a l r _ ihr =>
      rcases hs with ⟨rfl, hr⟩
      cases t with
      | nil =>
          simp only [inorder_node, inorder_nil, List.nil_append] at same
          cases same
      | node b l' r' =>
          rcases ht with ⟨rfl, hr'⟩
          simp only [inorder_node, inorder_nil, List.nil_append, List.cons.injEq] at same
          rcases same with ⟨rfl, tail⟩
          exact congrArg (fun q => BinaryTree.node a .nil q) (ihr hr hr' tail)

theorem listOf_eq_of_inorder_eq {s t : BinaryTree α} (same : inorder s = inorder t) :
    listOf s = listOf t :=
  eq_of_isList_of_inorder_eq (listOf_isList s) (listOf_isList t)
    ((listOf_inorder s).trans (same.trans (listOf_inorder t).symm))

theorem listOf_eq_self {t : BinaryTree α} (form : IsList t) : listOf t = t :=
  eq_of_isList_of_inorder_eq (listOf_isList t) form (listOf_inorder t)

theorem rightPositions_eq_nil {t : BinaryTree α} (form : IsList t) :
    rightPositions t = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [rightPositions_length, rightLength_eq_numNodes form, Nat.sub_self]

/-- Reversing the actual emitted positions makes every opposite step legal. -/
theorem reverse_rightPositions (t : BinaryTree α) :
    applyAts? rotateLeft? (rightPositions t).reverse (listOf t) = some t :=
  applyAts?_undo rotateRight? rotateLeft? rotateLeft?_undo _ (apply_rightPositions t)

/-- Two actual partial executions, with the second consuming the first result. -/
theorem connect_equal_inorder {s t : BinaryTree α} (same : inorder s = inorder t) :
    (applyAts? rotateRight? (rightPositions s) s).bind
      (applyAts? rotateLeft? (rightPositions t).reverse) = some t := by
  rw [apply_rightPositions, Option.bind_some, listOf_eq_of_inorder_eq same]
  exact reverse_rightPositions t

/-- Natural subtraction includes the common empty input without a special cost. -/
theorem connection_length_le {s t : BinaryTree α} (same : inorder s = inorder t) :
    (rightPositions s).length + (rightPositions t).length ≤ 2 * s.numNodes - 2 := by
  have hs := rightPositions_length_le_pred s
  have ht := rightPositions_length_le_pred t
  have sizes := numNodes_eq_of_inorder_eq same
  omega

/-- The accepted enumeration is precisely the observation class preserved by a trace. -/
theorem mem_enumTree_of_right_trace (xs : List α) (ps : List (List Branch))
    {s t : BinaryTree α} (member : s ∈ enumTree xs)
    (run : applyAts? rotateRight? ps s = some t) : t ∈ enumTree xs :=
  (mem_enumTree_iff xs t).mpr
    ((applyAts?_inorder rotateRight? rotateRight?_inorder ps run).trans
      ((mem_enumTree_iff xs s).mp member))

theorem connect_enumTree (xs : List α) {s t : BinaryTree α}
    (hs : s ∈ enumTree xs) (ht : t ∈ enumTree xs) :
    (applyAts? rotateRight? (rightPositions s) s).bind
      (applyAts? rotateLeft? (rightPositions t).reverse) = some t :=
  connect_equal_inorder (((mem_enumTree_iff xs s).mp hs).trans
    ((mem_enumTree_iff xs t).mp ht).symm)

theorem rightLength_leftChain (a : α) (n : Nat) :
    rightLength (leftChain a n) = if n = 0 then 0 else 1 := by
  cases n <;> rfl

theorem rightLength_rightChain (a : α) (n : Nat) : rightLength (rightChain a n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rightChain, rightLength_node, ih]

theorem isList_rightChain (a : α) (n : Nat) : IsList (rightChain a n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih⟩

theorem listOf_rightChain (a : α) (n : Nat) : listOf (rightChain a n) = rightChain a n :=
  listOf_eq_self (isList_rightChain a n)

theorem listOf_leftChain (a : α) (n : Nat) : listOf (leftChain a n) = rightChain a n := by
  apply eq_of_isList_of_inorder_eq (listOf_isList _) (isList_rightChain a n)
  rw [listOf_inorder, inorder_leftChain, inorder_rightChain]

theorem countRots_leftChain (a : α) (n : Nat) : countRots (leftChain a n) = n - 1 := by
  rw [countRots_eq_deficit, leftChain_numNodes, rightLength_leftChain]
  cases n <;> rfl

theorem countRots_rightChain (a : α) (n : Nat) : countRots (rightChain a n) = 0 := by
  rw [countRots_eq_deficit, rightChain_numNodes, rightLength_rightChain, Nat.sub_self]

/-- A list-form right tail leaves exactly the left chain's root rotations. -/
theorem rightPositions_leftChain_tail (a : α) (n : Nat) (r : BinaryTree α)
    (form : IsList r) :
    rightPositions (.node a (leftChain a n) r) = List.replicate n [] := by
  induction n generalizing r with
  | zero =>
      rw [leftChain, rightPositions_descend, rightPositions_eq_nil form]
      rfl
  | succ n ih =>
      rw [leftChain, rightPositions_rotate,
        ih (.node a .nil r) ⟨rfl, form⟩, List.replicate_succ]

theorem rightPositions_leftChain (a : α) (n : Nat) :
    rightPositions (leftChain a n) = List.replicate (n - 1) [] := by
  cases n with
  | zero => exact rightPositions_nil
  | succ n => exact rightPositions_leftChain_tail a n .nil trivial

theorem rightPositions_rightChain (a : α) (n : Nat) :
    rightPositions (rightChain a n) = [] :=
  rightPositions_eq_nil (isList_rightChain a n)

theorem measure_leftChain (a : α) (n : Nat) :
    measure (leftChain a n) = if n = 0 then 0 else 2 * n - 1 := by
  rw [measure, leftChain_numNodes, rightLength_leftChain]
  cases n <;> rfl

theorem measure_rightChain (a : α) (n : Nat) : measure (rightChain a n) = n := by
  rw [measure, rightChain_numNodes, rightLength_rightChain]
  omega

end Trees.Rotations
