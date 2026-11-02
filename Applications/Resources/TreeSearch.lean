import Applications.Resources.CallCount
import Applications.Trees.Ordered
import Mathlib.Order.Compare
import Lean.Elab.Tactic.Omega

/-! A selected-path query on the existing node-labelled tree. The returned
stored entry and the search-invocation observation come from one execution.
Visited nonempty nodes are derived from that result, with their own proved
recurrence. Comparator internals and nonrecursive projections are uncharged.
Source correspondence, model boundaries and attribution:
`docs/research/fdsa-tree-search.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeSearch
universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- Inspect one entry and follow only the selected child; every invocation
includes one entry charge, including an empty call or an immediate hit. -/
def run (route : α → Ordering) : BinaryTree α → Measured (Option α) Nat
  | .nil => CallCount.tick (Resources.pure none)
  | .node a l r =>
      match route a with
      | .lt => CallCount.tick (run route l)
      | .eq => CallCount.tick (Resources.pure (some a))
      | .gt => CallCount.tick (run route r)

abbrev find? (route : α → Ordering) (t : BinaryTree α) : Option α :=
  (run route t).1

abbrev entries (route : α → Ordering) (t : BinaryTree α) : Nat :=
  (run route t).2

/-- Remove the unique empty terminal invocation on failure. The recurrence
below establishes the visited-node meaning of this derived observation. -/
def visits (route : α → Ordering) (t : BinaryTree α) : Nat :=
  let result := run route t
  result.2 - (if result.1.isNone then 1 else 0)

@[simp] theorem run_nil (route : α → Ordering) :
    run route .nil = (none, 1) := rfl

theorem run_node (route : α → Ordering) (a : α) (l r : BinaryTree α) :
    run route (.node a l r) =
      match route a with
      | .lt => CallCount.tick (run route l)
      | .eq => CallCount.tick (Resources.pure (some a))
      | .gt => CallCount.tick (run route r) := rfl

theorem run_node_lt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .lt) :
    run route (.node a l r) = CallCount.tick (run route l) := by
  simp only [run, h]

theorem run_node_eq (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .eq) : run route (.node a l r) = (some a, 1) := by
  simp only [run, h, CallCount.tick, Resources.pure]

theorem run_node_gt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .gt) :
    run route (.node a l r) = CallCount.tick (run route r) := by
  simp only [run, h]

@[simp] theorem find?_nil (route : α → Ordering) :
    find? route .nil = none := rfl

theorem find?_node_lt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .lt) : find? route (.node a l r) = find? route l :=
  congrArg Prod.fst (run_node_lt route a l r h)

theorem find?_node_eq (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .eq) : find? route (.node a l r) = some a :=
  congrArg Prod.fst (run_node_eq route a l r h)

theorem find?_node_gt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .gt) : find? route (.node a l r) = find? route r :=
  congrArg Prod.fst (run_node_gt route a l r h)

@[simp] theorem entries_nil (route : α → Ordering) : entries route .nil = 1 := rfl

theorem entries_node_lt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .lt) : entries route (.node a l r) = entries route l + 1 :=
  congrArg Prod.snd (run_node_lt route a l r h)

theorem entries_node_eq (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .eq) : entries route (.node a l r) = 1 :=
  congrArg Prod.snd (run_node_eq route a l r h)

theorem entries_node_gt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .gt) : entries route (.node a l r) = entries route r + 1 :=
  congrArg Prod.snd (run_node_gt route a l r h)

theorem entries_pos (route : α → Ordering) (t : BinaryTree α) :
    1 ≤ entries route t := by
  cases t with
  | nil => exact Nat.le_refl 1
  | node a l r =>
      cases h : route a with
      | lt => rw [entries_node_lt route a l r h]; omega
      | eq => rw [entries_node_eq route a l r h]
      | gt => rw [entries_node_gt route a l r h]; omega

theorem entries_eq_visits_add_terminal (route : α → Ordering) (t : BinaryTree α) :
    entries route t = visits route t + (if (find? route t).isNone then 1 else 0) := by
  have h : (if (find? route t).isNone then 1 else 0) ≤ entries route t := by
    split
    · exact entries_pos route t
    · exact Nat.zero_le _
  exact (Nat.sub_add_cancel h).symm

theorem entries_eq_visits_of_some (route : α → Ordering) (t : BinaryTree α)
    (a : α) (h : find? route t = some a) : entries route t = visits route t := by
  simpa only [h, Option.isNone_some, Bool.false_eq_true, if_false, Nat.add_zero]
    using entries_eq_visits_add_terminal route t

theorem entries_eq_visits_add_one_of_none (route : α → Ordering) (t : BinaryTree α)
    (h : find? route t = none) : entries route t = visits route t + 1 := by
  simpa only [h, Option.isNone_none, if_true]
    using entries_eq_visits_add_terminal route t

@[simp] theorem visits_nil (route : α → Ordering) : visits route .nil = 0 := rfl

theorem visits_node_lt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .lt) : visits route (.node a l r) = visits route l + 1 := by
  have hn := entries_eq_visits_add_terminal route (.node a l r)
  have hl := entries_eq_visits_add_terminal route l
  rw [entries_node_lt route a l r h, find?_node_lt route a l r h] at hn
  omega

theorem visits_node_eq (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .eq) : visits route (.node a l r) = 1 := by
  have he := entries_eq_visits_of_some route (.node a l r) a
    (find?_node_eq route a l r h)
  rw [entries_node_eq route a l r h] at he
  exact he.symm

theorem visits_node_gt (route : α → Ordering) (a : α) (l r : BinaryTree α)
    (h : route a = .gt) : visits route (.node a l r) = visits route r + 1 := by
  have hn := entries_eq_visits_add_terminal route (.node a l r)
  have hr := entries_eq_visits_add_terminal route r
  rw [entries_node_gt route a l r h, find?_node_gt route a l r h] at hn
  omega

private theorem mem_inorder_left (root : α) (l r : BinaryTree α) (a : α)
    (h : a ∈ Trees.inorder l) : a ∈ Trees.inorder (.node root l r) := by
  rw [Trees.inorder_node, List.mem_append]
  exact Or.inl h

private theorem mem_inorder_root (root : α) (l r : BinaryTree α) :
    root ∈ Trees.inorder (.node root l r) := by
  simp only [Trees.inorder_node, List.mem_append, List.mem_cons, true_or, or_true]

private theorem mem_inorder_right (root : α) (l r : BinaryTree α) (a : α)
    (h : a ∈ Trees.inorder r) : a ∈ Trees.inorder (.node root l r) := by
  rw [Trees.inorder_node, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr h)

/-- A raw hit is a stored entry at which the actual route returned EQ. -/
theorem find?_some_spec (route : α → Ordering) (t : BinaryTree α) :
    ∀ a, find? route t = some a → a ∈ Trees.inorder t ∧ route a = .eq := by
  induction t with
  | nil => intro a h; cases h
  | node root l r ihl ihr =>
      intro a h
      cases hd : route root with
      | lt =>
          rw [find?_node_lt route root l r hd] at h
          rcases ihl a h with ⟨ha, heq⟩
          exact ⟨mem_inorder_left root l r a ha, heq⟩
      | eq =>
          rw [find?_node_eq route root l r hd] at h
          have heq : root = a := Option.some.inj h
          subst a
          exact ⟨mem_inorder_root root l r, hd⟩
      | gt =>
          rw [find?_node_gt route root l r hd] at h
          rcases ihr a h with ⟨ha, heq⟩
          exact ⟨mem_inorder_right root l r a ha, heq⟩

/-- Honest EQ soundness needs no search-tree invariant or order laws. -/
theorem key_eq_of_find?_eq_some [LT κ] (key : α → κ) (q : κ)
    (route : α → Ordering) (t : BinaryTree α) (a : α)
    (hRoute : ∀ b ∈ Trees.inorder t, (route b).Compares q (key b))
    (h : find? route t = some a) : key a = q := by
  rcases find?_some_spec route t a h with ⟨ha, heq⟩
  have hc := hRoute a ha
  rw [heq] at hc
  exact (show q = key a from hc).symm

private theorem find?_eq_some_of_mem [Preorder κ] (key : α → κ) (q : κ)
    (route : α → Ordering) (t : BinaryTree α) :
    Trees.Ordered (fun a b => key a < key b) t →
    (∀ b ∈ Trees.inorder t, (route b).Compares q (key b)) →
    ∀ a ∈ Trees.inorder t, key a = q → find? route t = some a := by
  induction t with
  | nil => intro _ _ a ha; cases ha
  | node root l r ihl ihr =>
      rintro ⟨hl, hr, hleft, hright⟩ hc a ha hkey
      have hcl : ∀ b ∈ Trees.inorder l, (route b).Compares q (key b) :=
        fun b hb => hc b (mem_inorder_left root l r b hb)
      have hcr : ∀ b ∈ Trees.inorder r, (route b).Compares q (key b) :=
        fun b hb => hc b (mem_inorder_right root l r b hb)
      have hcroot := hc root (mem_inorder_root root l r)
      rw [Trees.inorder_node, List.mem_append, List.mem_cons] at ha
      rcases ha with ha | heq | ha
      · have hd : route root = .lt := hcroot.eq_lt.2 (by
          rw [← hkey]
          exact hleft a ha)
        rw [find?_node_lt route root l r hd]
        exact ihl hl hcl a ha hkey
      · subst a
        have hd : route root = .eq := hcroot.eq_eq.2 hkey.symm
        exact find?_node_eq route root l r hd
      · have hd : route root = .gt := hcroot.eq_gt.2 (by
          rw [← hkey]
          exact hright a ha)
        rw [find?_node_gt route root l r hd]
        exact ihr hr hcr a ha hkey

/-- Strict key order gives full stored-entry correctness, not only key membership. -/
theorem find?_eq_some_iff [Preorder κ] (key : α → κ) (q : κ)
    (route : α → Ordering) (t : BinaryTree α)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t)
    (hRoute : ∀ b ∈ Trees.inorder t, (route b).Compares q (key b)) (a : α) :
    find? route t = some a ↔ a ∈ Trees.inorder t ∧ key a = q := by
  constructor
  · intro h
    exact ⟨(find?_some_spec route t a h).1,
      key_eq_of_find?_eq_some key q route t a hRoute h⟩
  · rintro ⟨ha, hkey⟩
    exact find?_eq_some_of_mem key q route t hOrdered hRoute a ha hkey

theorem find?_eq_none_iff [Preorder κ] (key : α → κ) (q : κ)
    (route : α → Ordering) (t : BinaryTree α)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t)
    (hRoute : ∀ b ∈ Trees.inorder t, (route b).Compares q (key b)) :
    find? route t = none ↔ ∀ a ∈ Trees.inorder t, key a ≠ q := by
  constructor
  · intro hnone a ha hkey
    have hs := (find?_eq_some_iff key q route t hOrdered hRoute a).2 ⟨ha, hkey⟩
    rw [hnone] at hs
    cases hs
  · intro h
    cases hf : find? route t with
    | none => rfl
    | some a =>
        rcases (find?_eq_some_iff key q route t hOrdered hRoute a).1 hf with ⟨ha, hkey⟩
        exact (h a ha hkey).elim

theorem find?_isSome_iff [Preorder κ] (key : α → κ) (q : κ)
    (route : α → Ordering) (t : BinaryTree α)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t)
    (hRoute : ∀ b ∈ Trees.inorder t, (route b).Compares q (key b)) :
    (find? route t).isSome ↔ ∃ a ∈ Trees.inorder t, key a = q := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (find?_eq_some_iff key q route t hOrdered hRoute a).1 ha⟩
  · rintro ⟨a, ha, hkey⟩
    exact ⟨a, (find?_eq_some_iff key q route t hOrdered hRoute a).2 ⟨ha, hkey⟩⟩

/-- The first matching inorder entry uses only the decidable EQ route result. -/
theorem find?_eq_find [Preorder κ] (key : α → κ) (q : κ)
    (route : α → Ordering) (t : BinaryTree α)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t)
    (hRoute : ∀ b ∈ Trees.inorder t, (route b).Compares q (key b)) :
    find? route t =
      (Trees.inorder t).find? (fun a => decide (route a = Ordering.eq)) := by
  cases hlist : (Trees.inorder t).find? (fun a => decide (route a = Ordering.eq)) with
  | none =>
      apply (find?_eq_none_iff key q route t hOrdered hRoute).2
      intro a ha hkey
      have heq : route a = .eq := (hRoute a ha).eq_eq.2 hkey.symm
      have hno := List.find?_eq_none.mp hlist a ha
      exact hno (by simp only [heq, decide_true])
  | some a =>
      have ha := List.mem_of_find?_eq_some hlist
      have heq : route a = .eq := of_decide_eq_true (List.find?_some hlist)
      have hkey := (hRoute a ha).eq_eq.1 heq
      exact (find?_eq_some_iff key q route t hOrdered hRoute a).2 ⟨ha, hkey.symm⟩

/-- Only the list observer needs lawful Boolean key equality; payloads are arbitrary. -/
theorem map_find?_eq_lookup [Preorder κ] [BEq κ] [LawfulBEq κ] (q : κ)
    (route : κ × β → Ordering) (t : BinaryTree (κ × β))
    (hOrdered : Trees.Ordered (fun a b => a.1 < b.1) t)
    (hRoute : ∀ b ∈ Trees.inorder t, (route b).Compares q b.1) :
    (find? route t).map Prod.snd = (Trees.inorder t).lookup q := by
  cases hlist : (Trees.inorder t).lookup q with
  | none =>
      have hf : find? route t = none :=
        (find?_eq_none_iff Prod.fst q route t hOrdered hRoute).2 (by
          intro a ha hkey
          have hno := List.lookup_eq_none_iff.mp hlist a ha
          simpa only [hkey, bne_self_eq_false, Bool.false_eq_true] using hno)
      rw [hf]
      rfl
  | some b =>
      rcases List.lookup_eq_some_iff.mp hlist with ⟨l₁, l₂, heq, _⟩
      have ha : (q, b) ∈ Trees.inorder t := by
        rw [heq]
        simp only [List.mem_append, List.mem_cons, true_or, or_true]
      have hf := (find?_eq_some_iff Prod.fst q route t hOrdered hRoute (q, b)).2 ⟨ha, rfl⟩
      rw [hf]
      rfl

/-- Local route agreement transports the actual chosen path and its observation. -/
theorem run_map (route : α → Ordering) (route' : β → Ordering) (f : α → β)
    (t : BinaryTree α)
    (h : ∀ a ∈ Trees.inorder t, route' (f a) = route a) :
    run route' (t.map f) = ((run route t).1.map f, (run route t).2) := by
  revert h
  induction t with
  | nil => intro _; rfl
  | node a l r ihl ihr =>
      intro h
      have ha := h a (mem_inorder_root a l r)
      have hl : ∀ b ∈ Trees.inorder l, route' (f b) = route b :=
        fun b hb => h b (mem_inorder_left a l r b hb)
      have hr : ∀ b ∈ Trees.inorder r, route' (f b) = route b :=
        fun b hb => h b (mem_inorder_right a l r b hb)
      cases hd : route a with
      | lt =>
          simpa only [BinaryTree.map, run, ha, hd, CallCount.tick]
            using congrArg CallCount.tick (ihl hl)
      | eq =>
          simp only [BinaryTree.map, run, ha, hd, CallCount.tick, Resources.pure,
            Option.map_some]
      | gt =>
          simpa only [BinaryTree.map, run, ha, hd, CallCount.tick]
            using congrArg CallCount.tick (ihr hr)

theorem run_map_pullback (route : β → Ordering) (f : α → β) (t : BinaryTree α) :
    run route (t.map f) =
      ((run (fun a => route (f a)) t).1.map f, (run (fun a => route (f a)) t).2) :=
  run_map (fun a => route (f a)) route f t (fun _ _ => rfl)

theorem find?_map (route : α → Ordering) (route' : β → Ordering) (f : α → β)
    (t : BinaryTree α) (h : ∀ a ∈ Trees.inorder t, route' (f a) = route a) :
    find? route' (t.map f) = (find? route t).map f :=
  congrArg Prod.fst (run_map route route' f t h)

theorem entries_map (route : α → Ordering) (route' : β → Ordering) (f : α → β)
    (t : BinaryTree α) (h : ∀ a ∈ Trees.inorder t, route' (f a) = route a) :
    entries route' (t.map f) = entries route t :=
  congrArg Prod.snd (run_map route route' f t h)

theorem visits_map (route : α → Ordering) (route' : β → Ordering) (f : α → β)
    (t : BinaryTree α) (h : ∀ a ∈ Trees.inorder t, route' (f a) = route a) :
    visits route' (t.map f) = visits route t := by
  unfold visits
  rw [run_map route route' f t h]
  simp only [Option.isNone_map]

theorem entries_le_height_add_one (route : α → Ordering) (t : BinaryTree α) :
    entries route t ≤ t.height + 1 := by
  induction t with
  | nil => exact Nat.le_refl 1
  | node a l r ihl ihr =>
      have hl := le_max_left l.height r.height
      have hr := le_max_right l.height r.height
      cases hd : route a with
      | lt =>
          rw [entries_node_lt route a l r hd]
          simp only [BinaryTree.height]
          omega
      | eq =>
          rw [entries_node_eq route a l r hd]
          simp only [BinaryTree.height]
          omega
      | gt =>
          rw [entries_node_gt route a l r hd]
          simp only [BinaryTree.height]
          omega

theorem entries_le_height_of_some (route : α → Ordering) (t : BinaryTree α) :
    ∀ a, find? route t = some a → entries route t ≤ t.height := by
  induction t with
  | nil => intro a h; cases h
  | node root l r ihl ihr =>
      intro a h
      have hl := le_max_left l.height r.height
      have hr := le_max_right l.height r.height
      cases hd : route root with
      | lt =>
          rw [find?_node_lt route root l r hd] at h
          have hb := ihl a h
          rw [entries_node_lt route root l r hd]
          simp only [BinaryTree.height]
          omega
      | eq =>
          rw [entries_node_eq route root l r hd]
          simp only [BinaryTree.height]
          omega
      | gt =>
          rw [find?_node_gt route root l r hd] at h
          have hb := ihr a h
          rw [entries_node_gt route root l r hd]
          simp only [BinaryTree.height]
          omega

theorem visits_le_height (route : α → Ordering) (t : BinaryTree α) :
    visits route t ≤ t.height := by
  cases h : find? route t with
  | none =>
      have hb := entries_le_height_add_one route t
      have he := entries_eq_visits_add_one_of_none route t h
      omega
  | some a =>
      have hb := entries_le_height_of_some route t a h
      have he := entries_eq_visits_of_some route t a h
      omega

theorem visits_pos_of_some (route : α → Ordering) (t : BinaryTree α)
    (a : α) (h : find? route t = some a) : 1 ≤ visits route t := by
  rw [← entries_eq_visits_of_some route t a h]
  exact entries_pos route t

/-- A deepest stored key realizes the tree height. Only comparisons between
stored entries are calibrated; no default query or payload is required. -/
theorem exists_run_eq_height [Preorder κ] (key : α → κ)
    (route : κ → α → Ordering) (t : BinaryTree α) (ht : t ≠ .nil)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t)
    (hRoute : ∀ a ∈ Trees.inorder t, ∀ b ∈ Trees.inorder t,
      (route (key a) b).Compares (key a) (key b)) :
    ∃ a ∈ Trees.inorder t, run (route (key a)) t = (some a, t.height) := by
  revert ht hOrdered hRoute
  induction t with
  | nil => intro ht _ _; exact (ht rfl).elim
  | node root l r ihl ihr =>
      rintro _ ⟨hl, hr, hleft, hright⟩ hc
      have hcl : ∀ a ∈ Trees.inorder l, ∀ b ∈ Trees.inorder l,
          (route (key a) b).Compares (key a) (key b) :=
        fun a ha b hb => hc a (mem_inorder_left root l r a ha)
          b (mem_inorder_left root l r b hb)
      have hcr : ∀ a ∈ Trees.inorder r, ∀ b ∈ Trees.inorder r,
          (route (key a) b).Compares (key a) (key b) :=
        fun a ha b hb => hc a (mem_inorder_right root l r a ha)
          b (mem_inorder_right root l r b hb)
      by_cases hlnil : l = .nil
      · by_cases hrnil : r = .nil
        · have hd : route (key root) root = .eq :=
            (hc root (mem_inorder_root root l r)
              root (mem_inorder_root root l r)).eq_eq.2 rfl
          refine ⟨root, mem_inorder_root root l r, ?_⟩
          rw [run_node_eq (route (key root)) root l r hd]
          simp only [hlnil, hrnil, BinaryTree.height, Nat.max_self]
        · obtain ⟨a, ha, hrun⟩ := ihr hrnil hr hcr
          have hd : route (key a) root = .gt :=
            (hc a (mem_inorder_right root l r a ha)
              root (mem_inorder_root root l r)).eq_gt.2 (hright a ha)
          refine ⟨a, mem_inorder_right root l r a ha, ?_⟩
          rw [run_node_gt (route (key a)) root l r hd, hrun]
          simp only [CallCount.tick, BinaryTree.height, hlnil, Nat.zero_max]
      · by_cases hmax : r.height ≤ l.height
        · obtain ⟨a, ha, hrun⟩ := ihl hlnil hl hcl
          have hd : route (key a) root = .lt :=
            (hc a (mem_inorder_left root l r a ha)
              root (mem_inorder_root root l r)).eq_lt.2 (hleft a ha)
          refine ⟨a, mem_inorder_left root l r a ha, ?_⟩
          rw [run_node_lt (route (key a)) root l r hd, hrun]
          simp only [CallCount.tick, BinaryTree.height, Nat.max_eq_left hmax]
        · have hrnil : r ≠ .nil := by
            intro heq
            subst r
            simp only [BinaryTree.height, Nat.zero_le] at hmax
          obtain ⟨a, ha, hrun⟩ := ihr hrnil hr hcr
          have hd : route (key a) root = .gt :=
            (hc a (mem_inorder_right root l r a ha)
              root (mem_inorder_root root l r)).eq_gt.2 (hright a ha)
          have hmax' : l.height ≤ r.height := by omega
          refine ⟨a, mem_inorder_right root l r a ha, ?_⟩
          rw [run_node_gt (route (key a)) root l r hd, hrun]
          simp only [CallCount.tick, BinaryTree.height, Nat.max_eq_right hmax']

theorem exists_run_visits_eq_height [Preorder κ] (key : α → κ)
    (route : κ → α → Ordering) (t : BinaryTree α) (ht : t ≠ .nil)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t)
    (hRoute : ∀ a ∈ Trees.inorder t, ∀ b ∈ Trees.inorder t,
      (route (key a) b).Compares (key a) (key b)) :
    ∃ a ∈ Trees.inorder t,
      run (route (key a)) t = (some a, t.height) ∧
        visits (route (key a)) t = t.height := by
  obtain ⟨a, ha, hrun⟩ := exists_run_eq_height key route t ht hOrdered hRoute
  have hf : find? (route (key a)) t = some a := congrArg Prod.fst hrun
  have he : entries (route (key a)) t = t.height := congrArg Prod.snd hrun
  exact ⟨a, ha, hrun, (entries_eq_visits_of_some (route (key a)) t a hf).symm.trans he⟩

theorem exists_source_run_eq_height [LinearOrder κ] (key : α → κ)
    (t : BinaryTree α) (ht : t ≠ .nil)
    (hOrdered : Trees.Ordered (fun a b => key a < key b) t) :
    ∃ a ∈ Trees.inorder t,
      run (fun b => compareOfLessAndEq (key a) (key b)) t = (some a, t.height) ∧
        visits (fun b => compareOfLessAndEq (key a) (key b)) t = t.height := by
  apply exists_run_visits_eq_height key (fun q a => compareOfLessAndEq q (key a))
    t ht hOrdered
  intro a _ b _
  simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares (key a) (key b)

end Resources.TreeSearch
