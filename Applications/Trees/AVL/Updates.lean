import Applications.Trees.AVL.Rebalance
import Applications.Trees.HeightBalance.OrderedUpdates

/-! Cached AVL updates are the tolerance-one specialization of the complete
annotation programs. Raw recurrence, cache correctness, shape balance and
ordered observations retain their separate assumptions. Source correspondence:
`docs/research/fdsa-height-updates.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.AVL
universe u
variable {α : Type u}

/-- Insert using the existing cached tolerance-one local balancers. -/
def insert [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    BinaryTree (α × Nat) := HeightBalance.insert heightAnnotation 1 x t

/-- Remove the rightmost payload, returning the remaining tree first. -/
def splitMaxOption (t : BinaryTree (α × Nat)) :
    Option (BinaryTree (α × Nat) × α) :=
  HeightBalance.splitMaxOption heightAnnotation 1 t

/-- Delete by replacing an equal root with its left-subtree predecessor. -/
def delete [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    BinaryTree (α × Nat) := HeightBalance.delete heightAnnotation 1 x t

@[simp] theorem insert_nil [LT α] [DecidableLT α] (x : α) :
    insert x .nil = node .nil x .nil :=
  HeightBalance.insert_nil heightAnnotation 1 x

theorem insert_node [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    insert x (.node (a, n) l r) =
      if x < a then balL (insert x l) a r
      else if a < x then balR l a (insert x r)
      else .node (a, n) l r :=
  HeightBalance.insert_node heightAnnotation 1 x a n l r

theorem insert_of_lt [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hxa : x < a) :
    insert x (.node (a, n) l r) = balL (insert x l) a r :=
  HeightBalance.insert_of_lt heightAnnotation 1 x a n l r hxa

theorem insert_of_gt [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hxa : ¬ x < a) (hax : a < x) :
    insert x (.node (a, n) l r) = balR l a (insert x r) :=
  HeightBalance.insert_of_gt heightAnnotation 1 x a n l r hxa hax

/-- Both guards are needed for an arbitrary decidable relation. -/
theorem insert_of_not_lt_of_not_lt [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hxa : ¬ x < a) (hax : ¬ a < x) :
    insert x (.node (a, n) l r) = .node (a, n) l r :=
  HeightBalance.insert_of_not_lt_of_not_lt heightAnnotation 1 x a n l r hxa hax

@[simp] theorem splitMaxOption_nil :
    splitMaxOption (.nil : BinaryTree (α × Nat)) = none :=
  HeightBalance.splitMaxOption_nil heightAnnotation 1

theorem splitMaxOption_node_nil (a : α) (n : Nat) (l : BinaryTree (α × Nat)) :
    splitMaxOption (.node (a, n) l .nil) = some (l, a) :=
  HeightBalance.splitMaxOption_node_nil heightAnnotation 1 a n l

theorem splitMaxOption_node_of_ne_nil (a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hr : r ≠ .nil) :
    splitMaxOption (.node (a, n) l r) =
      (splitMaxOption r).map (fun p => (balL l a p.1, p.2)) :=
  HeightBalance.splitMaxOption_node_of_ne_nil heightAnnotation 1 a n l r hr

theorem splitMaxOption_node_of_some (a : α) (n : Nat)
    (l r r' : BinaryTree (α × Nat)) (m : α)
    (hs : splitMaxOption r = some (r', m)) :
    splitMaxOption (.node (a, n) l r) = some (balL l a r', m) :=
  HeightBalance.splitMaxOption_node_of_some heightAnnotation 1 a n l r r' m hs

theorem splitMaxOption_eq_none_iff (t : BinaryTree (α × Nat)) :
    splitMaxOption t = none ↔ t = .nil :=
  HeightBalance.splitMaxOption_eq_none_iff heightAnnotation 1 t

theorem splitMaxOption_exists_of_ne_nil (t : BinaryTree (α × Nat)) (ht : t ≠ .nil) :
    ∃ t' m, splitMaxOption t = some (t', m) :=
  HeightBalance.splitMaxOption_exists_of_ne_nil heightAnnotation 1 t ht

@[simp] theorem delete_nil [LT α] [DecidableLT α] (x : α) :
    delete x .nil = .nil := HeightBalance.delete_nil heightAnnotation 1 x

theorem delete_node [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    delete x (.node (a, n) l r) =
      if x < a then balR (delete x l) a r
      else if a < x then balL l a (delete x r)
      else match splitMaxOption l with
        | none => r
        | some (l', m) => balR l' m r := by
  have h := HeightBalance.delete_node heightAnnotation 1 x a n l r
  cases hs : HeightBalance.splitMaxOption heightAnnotation 1 l with
  | none => simpa only [delete, splitMaxOption, balL, balR, hs] using h
  | some p =>
      rcases p with ⟨l', m⟩
      simpa only [delete, splitMaxOption, balL, balR, hs] using h

theorem delete_of_lt [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hxa : x < a) :
    delete x (.node (a, n) l r) = balR (delete x l) a r :=
  HeightBalance.delete_of_lt heightAnnotation 1 x a n l r hxa

theorem delete_of_gt [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hxa : ¬ x < a) (hax : a < x) :
    delete x (.node (a, n) l r) = balL l a (delete x r) :=
  HeightBalance.delete_of_gt heightAnnotation 1 x a n l r hxa hax

theorem delete_of_not_lt_of_not_lt [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hxa : ¬ x < a) (hax : ¬ a < x) :
    delete x (.node (a, n) l r) =
      match splitMaxOption l with
      | none => r
      | some (l', m) => balR l' m r := by
  have h := HeightBalance.delete_of_not_lt_of_not_lt heightAnnotation 1 x a n l r hxa hax
  cases hs : HeightBalance.splitMaxOption heightAnnotation 1 l with
  | none => simpa only [delete, splitMaxOption, balR, hs] using h
  | some p =>
      rcases p with ⟨l', m⟩
      simpa only [delete, splitMaxOption, balR, hs] using h

theorem cacheValid_insert [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (hc : CacheValid t) : CacheValid (insert x t) :=
  HeightBalance.cacheValid_insert heightAnnotation 1 x t hc

theorem cacheValid_splitMaxOption (t t' : BinaryTree (α × Nat)) (m : α)
    (hs : splitMaxOption t = some (t', m)) (hc : CacheValid t) : CacheValid t' :=
  HeightBalance.cacheValid_splitMaxOption heightAnnotation 1 t t' m hs hc

theorem cacheValid_delete [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (hc : CacheValid t) : CacheValid (delete x t) :=
  HeightBalance.cacheValid_delete heightAnnotation 1 x t hc

/-- The raw extraction observation needs no cache, balance or ordering premise. -/
theorem inorder_splitMaxOption (t t' : BinaryTree (α × Nat)) (m : α)
    (hs : splitMaxOption t = some (t', m)) :
    Trees.inorder (Cached.erase t') ++ [m] = Trees.inorder (Cached.erase t) :=
  HeightBalance.inorder_splitMaxOption heightAnnotation 1 t t' m hs

theorem valid_insert [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (hv : Valid t) :
    Valid (insert x t) ∧
      ((insert x t).height = t.height ∨ (insert x t).height = t.height + 1) := by
  have h := HeightBalance.validD_insert heightAnnotation 1 x t (by decide)
    ((validD_one_iff t).mpr hv)
  exact ⟨(validD_one_iff _).mp h.1, h.2⟩

theorem valid_splitMaxOption (t t' : BinaryTree (α × Nat)) (m : α)
    (hs : splitMaxOption t = some (t', m)) (hv : Valid t) :
    Valid t' ∧ (t.height = t'.height ∨ t.height = t'.height + 1) := by
  have h := HeightBalance.validD_splitMaxOption heightAnnotation 1 t t' m hs (by decide)
    ((validD_one_iff t).mpr hv)
  exact ⟨(validD_one_iff _).mp h.1, h.2⟩

theorem valid_delete [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (hv : Valid t) :
    Valid (delete x t) ∧
      (t.height = (delete x t).height ∨ t.height = (delete x t).height + 1) := by
  have h := HeightBalance.validD_delete heightAnnotation 1 x t (by decide)
    ((validD_one_iff t).mpr hv)
  exact ⟨(validD_one_iff _).mp h.1, h.2⟩

theorem inorder_insert [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hs : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Trees.inorder (Cached.erase (insert x t)) =
      Search.OrderedList.insert x (Trees.inorder (Cached.erase t)) :=
  HeightBalance.inorder_insert heightAnnotation 1 x t hs

theorem inorder_delete [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hs : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Trees.inorder (Cached.erase (delete x t)) =
      Search.OrderedList.delete x (Trees.inorder (Cached.erase t)) :=
  HeightBalance.inorder_delete heightAnnotation 1 x t hs

theorem strict_inorder_insert [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hs : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedList.Strict (Trees.inorder (Cached.erase (insert x t))) :=
  HeightBalance.strict_inorder_insert heightAnnotation 1 x t hs

theorem strict_inorder_delete [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hs : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedList.Strict (Trees.inorder (Cached.erase (delete x t))) :=
  HeightBalance.strict_inorder_delete heightAnnotation 1 x t hs

theorem strict_inorder_splitMaxOption [LT α]
    (t t' : BinaryTree (α × Nat)) (m : α)
    (hs : splitMaxOption t = some (t', m))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedList.Strict (Trees.inorder (Cached.erase t')) ∧
      ∀ x ∈ Trees.inorder (Cached.erase t'), x < m :=
  HeightBalance.strict_inorder_splitMaxOption heightAnnotation 1 t t' m hs hstrict

theorem maximal_splitMaxOption [Preorder α]
    (t t' : BinaryTree (α × Nat)) (m : α)
    (hs : splitMaxOption t = some (t', m))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    m ∈ Trees.inorder (Cached.erase t) ∧
      ∀ x ∈ Trees.inorder (Cached.erase t), x ≤ m :=
  HeightBalance.maximal_splitMaxOption heightAnnotation 1 t t' m hs hstrict

end Trees.AVL
