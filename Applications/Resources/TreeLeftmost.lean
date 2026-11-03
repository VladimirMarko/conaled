import Applications.Resources.CallCount
import Applications.Trees.Ordered
import Mathlib.Order.Bounds.Defs

/-! Ordinary leftmost extraction from the existing node-labelled binary tree.
The measured execution stops at a node whose left child is empty and returns
its actual right child. Only extractor invocations are charged; construction,
shape tests and observations are uncharged in this declared model. The empty
result `(none, 1)` is a total Lean extension of the source's unspecified case.
Source correspondence, the applicable notice and remaining work are recorded
in `docs/research/fdsa-tree-leftmost.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeLeftmost
universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- Extract the first inorder label and the actual residual tree, visiting
only the nonempty left spine on a successful input. -/
def run : BinaryTree α → Measured (Option (α × BinaryTree α)) Nat
  | .nil => CallCount.tick (Resources.pure none)
  | .node a .nil r => CallCount.tick (Resources.pure (some (a, r)))
  | .node a (.node b ll lr) r =>
      CallCount.tick (Resources.bind (run (.node b ll lr)) (fun result =>
        Resources.pure (result.map (fun (m, l') => (m, .node a l' r)))))

/-- The value observation of the same measured execution. -/
def extract? (t : BinaryTree α) : Option (α × BinaryTree α) := (run t).1

/-- Invocation count of the same measured execution, including the chosen
one-entry empty extension. -/
def entries (t : BinaryTree α) : Nat := (run t).2

theorem run_eq (t : BinaryTree α) : run t = (extract? t, entries t) := rfl

@[simp] theorem run_nil : run (.nil : BinaryTree α) = (none, 1) := rfl

@[simp] theorem run_node_nil (a : α) (r : BinaryTree α) :
    run (.node a .nil r) = (some (a, r), 1) := rfl

theorem run_node_node (a b : α) (ll lr r : BinaryTree α) :
    run (.node a (.node b ll lr) r) =
      ((run (.node b ll lr)).1.map (fun (m, l') => (m, .node a l' r)),
        (run (.node b ll lr)).2 + 1) := rfl

theorem run_node_of_ne_nil (a : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
    run (.node a l r) =
      ((run l).1.map (fun (m, l') => (m, .node a l' r)), (run l).2 + 1) := by
  cases l with
  | nil => exact (hl rfl).elim
  | node b ll lr => exact run_node_node a b ll lr r

/-- The parent consumes both the actual removed label and the actual residual
of its successful child execution; the untouched right fringe is retained. -/
theorem run_node_of_run (a : α) (l r : BinaryTree α) (m : α)
    (l' : BinaryTree α) (cost : Nat) (h : run l = (some (m, l'), cost)) :
    run (.node a l r) = (some (m, .node a l' r), cost + 1) := by
  cases l with
  | nil =>
      have hn : (none : Option (α × BinaryTree α)) = some (m, l') :=
        congrArg Prod.fst h
      cases hn
  | node b ll lr =>
      simpa only [h, Option.map_some] using run_node_node a b ll lr r

@[simp] theorem extract?_nil : extract? (.nil : BinaryTree α) = none := rfl

@[simp] theorem extract?_node_nil (a : α) (r : BinaryTree α) :
    extract? (.node a .nil r) = some (a, r) := rfl

theorem extract?_node_node (a b : α) (ll lr r : BinaryTree α) :
    extract? (.node a (.node b ll lr) r) =
      (extract? (.node b ll lr)).map (fun (m, l') => (m, .node a l' r)) := rfl

theorem extract?_node_of_ne_nil (a : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
    extract? (.node a l r) =
      (extract? l).map (fun (m, l') => (m, .node a l' r)) :=
  congrArg Prod.fst (run_node_of_ne_nil a l r hl)

theorem extract?_node_of_extract? (a : α) (l r : BinaryTree α) (m : α)
    (l' : BinaryTree α) (h : extract? l = some (m, l')) :
    extract? (.node a l r) = some (m, .node a l' r) := by
  have hr : run l = (some (m, l'), entries l) := Prod.ext h rfl
  exact congrArg Prod.fst (run_node_of_run a l r m l' (entries l) hr)

@[simp] theorem entries_nil : entries (.nil : BinaryTree α) = 1 := rfl

@[simp] theorem entries_node_nil (a : α) (r : BinaryTree α) :
    entries (.node a .nil r) = 1 := rfl

theorem entries_node_node (a b : α) (ll lr r : BinaryTree α) :
    entries (.node a (.node b ll lr) r) = entries (.node b ll lr) + 1 := rfl

theorem entries_node_of_ne_nil (a : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
    entries (.node a l r) = entries l + 1 :=
  congrArg Prod.snd (run_node_of_ne_nil a l r hl)

/-- Success is defined on every nonempty raw tree, independently of order. -/
@[simp] theorem extract?_eq_none_iff (t : BinaryTree α) :
    extract? t = none ↔ t = .nil := by
  induction t with
  | nil => simp
  | node a l r ihl _ihr =>
      cases l with
      | nil => simp
      | node b ll lr =>
          rw [extract?_node_node, Option.map_eq_none_iff, ihl]
          simp

theorem exists_extract?_of_ne_nil (t : BinaryTree α) (ht : t ≠ .nil) :
    ∃ m r, extract? t = some (m, r) := by
  cases h : extract? t with
  | none => exact (ht ((extract?_eq_none_iff t).1 h)).elim
  | some pair => exact ⟨pair.1, pair.2, h⟩

theorem extract?_isSome_iff (t : BinaryTree α) :
    (extract? t).isSome = true ↔ t ≠ .nil :=
  Option.isSome_iff_ne_none.trans (not_congr (extract?_eq_none_iff t))

theorem ne_nil_of_extract? (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) : t ≠ .nil := by
  intro ht
  subst t
  cases h

/-- The actual returned pair removes exactly the first inorder occurrence.
This does not identify an arbitrary residual tree from its inorder alone. -/
theorem inorder_of_extract? (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) : m :: Trees.inorder r = Trees.inorder t := by
  revert m r h
  induction t with
  | nil =>
      intro m r h
      cases h
  | node a l r ihl _ihr =>
      intro m s h
      cases l with
      | nil =>
          rw [extract?_node_nil] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨hm, hs⟩
          subst m
          subst s
          rfl
      | node b ll lr =>
          obtain ⟨m', l', hl⟩ := exists_extract?_of_ne_nil
            (.node b ll lr) (by intro hn; cases hn)
          rw [extract?_node_of_extract? a (.node b ll lr) r m' l' hl] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨hm, hs⟩
          subst m
          subst s
          calc
            m' :: Trees.inorder (.node a l' r) =
                (m' :: Trees.inorder l') ++ (a :: Trees.inorder r) := rfl
            _ = Trees.inorder (.node b ll lr) ++ (a :: Trees.inorder r) :=
                congrArg (fun xs => xs ++ (a :: Trees.inorder r)) (ihl m' l' hl)
            _ = Trees.inorder (.node a (.node b ll lr) r) := rfl

theorem mem_inorder_iff (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) (a : α) :
    a ∈ Trees.inorder t ↔ a = m ∨ a ∈ Trees.inorder r := by
  rw [← inorder_of_extract? t m r h]
  exact List.mem_cons

theorem extracted_mem_inorder (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) : m ∈ Trees.inorder t :=
  (mem_inorder_iff t m r h m).2 (Or.inl rfl)

theorem residual_mem_inorder (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) (a : α) (ha : a ∈ Trees.inorder r) :
    a ∈ Trees.inorder t :=
  (mem_inorder_iff t m r h a).2 (Or.inr ha)

theorem head?_inorder_of_extract? (t : BinaryTree α) (m : α)
    (r : BinaryTree α) (h : extract? t = some (m, r)) :
    (Trees.inorder t).head? = some m :=
  congrArg List.head? (inorder_of_extract? t m r h).symm

theorem tail_inorder_of_extract? (t : BinaryTree α) (m : α)
    (r : BinaryTree α) (h : extract? t = some (m, r)) :
    (Trees.inorder t).tail = Trees.inorder r :=
  congrArg List.tail (inorder_of_extract? t m r h).symm

/-- This is an occurrence count, obtained from the existing inorder length. -/
theorem numNodes_of_extract? (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) : r.numNodes + 1 = t.numNodes := by
  simpa only [List.length_cons, Trees.inorder_length] using
    congrArg List.length (inorder_of_extract? t m r h)

/-- Height nonincrease follows from the actual splice, not inorder equality. -/
theorem height_of_extract? (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (h : extract? t = some (m, r)) : r.height ≤ t.height := by
  revert m r h
  induction t with
  | nil =>
      intro m r h
      cases h
  | node a l r ihl _ihr =>
      intro m s h
      cases l with
      | nil =>
          rw [extract?_node_nil] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨hm, hs⟩
          subst m
          subst s
          change r.height ≤ max 0 r.height + 1
          exact le_trans (le_max_right _ _) (Nat.le_succ _)
      | node b ll lr =>
          obtain ⟨m', l', hl⟩ := exists_extract?_of_ne_nil
            (.node b ll lr) (by intro hn; cases hn)
          rw [extract?_node_of_extract? a (.node b ll lr) r m' l' hl] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨hm, hs⟩
          subst m
          subst s
          change max l'.height r.height + 1 ≤
            max (BinaryTree.node b ll lr).height r.height + 1
          exact Nat.add_le_add_right
            (max_le (le_trans (ihl m' l' hl) (le_max_left _ _))
              (le_max_right _ _)) 1

/-- Label-blind control transports the complete returned pair and its count.
This does not include the work of separately constructing the mapped input. -/
theorem run_map (f : α → β) (t : BinaryTree α) :
    run (t.map f) =
      ((run t).1.map (fun (m, r) => (f m, r.map f)), (run t).2) := by
  induction t with
  | nil => rfl
  | node a l r ihl _ihr =>
      cases l with
      | nil => rfl
      | node b ll lr =>
          change
            ((run ((.node b ll lr : BinaryTree α).map f)).1.map
                (fun (m, l') => (m, .node (f a) l' (r.map f))),
              (run ((.node b ll lr : BinaryTree α).map f)).2 + 1) =
            (((run (.node b ll lr)).1.map
                (fun (m, l') => (m, .node a l' r))).map
                (fun (m, s) => (f m, s.map f)),
              (run (.node b ll lr)).2 + 1)
          simp only [ihl]
          cases (run (.node b ll lr)).1 with
          | none => rfl
          | some pair =>
              cases pair
              rfl

theorem extract?_map (f : α → β) (t : BinaryTree α) :
    extract? (t.map f) = (extract? t).map (fun (m, r) => (f m, r.map f)) :=
  congrArg Prod.fst (run_map f t)

theorem entries_map (f : α → β) (t : BinaryTree α) :
    entries (t.map f) = entries t := congrArg Prod.snd (run_map f t)

/-- Every ancestor retains its bounds after the actual residual is spliced in.
This preservation statement needs no transitivity of the relation. -/
theorem ordered_of_extract? (R : α → α → Prop) (t : BinaryTree α)
    (m : α) (r : BinaryTree α) (ht : Trees.Ordered R t)
    (h : extract? t = some (m, r)) : Trees.Ordered R r := by
  revert m r ht h
  induction t with
  | nil =>
      intro m r _ht h
      cases h
  | node a l r ihl _ihr =>
      intro m s ht h
      rcases ht with ⟨hl_order, hr_order, hl_root, hr_root⟩
      cases l with
      | nil =>
          rw [extract?_node_nil] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨hm, hs⟩
          subst m
          subst s
          exact hr_order
      | node b ll lr =>
          obtain ⟨m', l', hl⟩ := exists_extract?_of_ne_nil
            (.node b ll lr) (by intro hn; cases hn)
          rw [extract?_node_of_extract? a (.node b ll lr) r m' l' hl] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨hm, hs⟩
          subst m
          subst s
          exact ⟨ihl m' l' hl_order hl, hr_order,
            fun x hx => hl_root x (residual_mem_inorder (.node b ll lr) m' l' hl x hx),
            hr_root⟩

/-- Relating the removed label to every residual label uses transitivity,
unlike preservation of the recursive structural invariant. -/
theorem rel_of_extract? (R : α → α → Prop) (hR : Transitive R)
    (t : BinaryTree α) (m : α) (r : BinaryTree α) (ht : Trees.Ordered R t)
    (h : extract? t = some (m, r)) (b : α) (hb : b ∈ Trees.inorder r) : R m b := by
  have hp := Trees.pairwise_inorder_of_ordered R hR t ht
  rw [← inorder_of_extract? t m r h] at hp
  exact List.rel_of_pairwise_cons hp hb

theorem key_lt_of_extract? [Preorder κ] (key : α → κ) (t : BinaryTree α)
    (m : α) (r : BinaryTree α) (ht : Trees.Ordered (fun a b => key a < key b) t)
    (h : extract? t = some (m, r)) (b : α) (hb : b ∈ Trees.inorder r) :
    key m < key b :=
  rel_of_extract? (fun a b => key a < key b)
    (fun _ _ _ hab hbc => lt_trans hab hbc) t m r ht h b hb

theorem isLeast_key_of_extract? [Preorder κ] (key : α → κ)
    (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (ht : Trees.Ordered (fun a b => key a < key b) t)
    (h : extract? t = some (m, r)) :
    IsLeast {q | q ∈ (Trees.inorder t).map key} (key m) := by
  refine ⟨List.mem_map_of_mem (extracted_mem_inorder t m r h), ?_⟩
  intro q hq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  rcases (mem_inorder_iff t m r h b).1 hb with hm | hr
  · subst b
    exact le_rfl
  · exact le_of_lt (key_lt_of_extract? key t m r ht h b hr)

theorem key_not_mem_of_extract? [Preorder κ] (key : α → κ)
    (t : BinaryTree α) (m : α) (r : BinaryTree α)
    (ht : Trees.Ordered (fun a b => key a < key b) t)
    (h : extract? t = some (m, r)) : key m ∉ (Trees.inorder r).map key := by
  intro hm
  obtain ⟨b, hb, hkey⟩ := List.mem_map.mp hm
  exact (ne_of_lt (key_lt_of_extract? key t m r ht h b hb)) hkey.symm

/-- Exact key removal is a strict-order consequence, not a raw set law. -/
theorem mem_key_inorder_iff [Preorder κ] (key : α → κ) (t : BinaryTree α)
    (m : α) (r : BinaryTree α) (ht : Trees.Ordered (fun a b => key a < key b) t)
    (h : extract? t = some (m, r)) (q : κ) :
    q ∈ (Trees.inorder r).map key ↔
      q ∈ (Trees.inorder t).map key ∧ q ≠ key m := by
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · rw [← inorder_of_extract? t m r h, List.map_cons]
      exact List.mem_cons_of_mem _ hq
    · intro heq
      exact key_not_mem_of_extract? key t m r ht h (heq ▸ hq)
  · rintro ⟨hq, hne⟩
    rw [← inorder_of_extract? t m r h, List.map_cons, List.mem_cons] at hq
    exact hq.resolve_left hne

theorem one_le_entries (t : BinaryTree α) : 1 ≤ entries t := by
  cases t with
  | nil => exact le_rfl
  | node a l r =>
      cases l with
      | nil => exact le_rfl
      | node b ll lr =>
          change 1 ≤ entries (.node b ll lr) + 1
          exact Nat.succ_le_succ (Nat.zero_le _)

/-- Successful source calls stop before nil, so height itself is sufficient. -/
theorem entries_le_height (t : BinaryTree α) (ht : t ≠ .nil) :
    entries t ≤ t.height := by
  revert ht
  induction t with
  | nil =>
      intro ht
      exact (ht rfl).elim
  | node a l r ihl _ihr =>
      intro _ht
      cases l with
      | nil =>
          change 1 ≤ max 0 r.height + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
      | node b ll lr =>
          have hl : entries (.node b ll lr) ≤ (BinaryTree.node b ll lr).height :=
            ihl (by intro hn; cases hn)
          change entries (.node b ll lr) + 1 ≤
            max (BinaryTree.node b ll lr).height r.height + 1
          exact Nat.add_le_add_right (le_trans hl (le_max_left _ _)) 1

theorem entries_le_height_of_extract? (t : BinaryTree α) (m : α)
    (r : BinaryTree α) (h : extract? t = some (m, r)) : entries t ≤ t.height :=
  entries_le_height t (ne_nil_of_extract? t m r h)

theorem entries_le_numNodes (t : BinaryTree α) (ht : t ≠ .nil) :
    entries t ≤ t.numNodes :=
  le_trans (entries_le_height t ht) (BinaryTree.height_le_numNodes t)

/-- The all-input bound includes the explicitly selected empty charge. -/
theorem entries_le_height_add_one (t : BinaryTree α) :
    entries t ≤ t.height + 1 := by
  cases t with
  | nil => exact le_rfl
  | node a l r =>
      exact le_trans (entries_le_height (.node a l r) (by intro h; cases h))
        (Nat.le_succ _)

end Resources.TreeLeftmost
