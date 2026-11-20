import Applications.Trees.HeightBalance.Rebalance

/-! Complete-annotation insertion, optional rightmost extraction, and predecessor
deletion. Raw programs use only decidable comparison where a query is present.
Cache and extraction-inorder laws hold at every natural tolerance; simultaneous
balance and actual-height laws require a positive tolerance. Ordered observations
are supplied separately by `HeightBalance.OrderedUpdates`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.HeightBalance
universe u v
variable {α : Type u} {σ : Type v}

/-- Rebuild every changed ancestor's complete summary; the final comparison
branch returns the original raw node, including its original annotation. -/
def insert [LT α] [DecidableLT α] (ann : HeightAnnotation α σ) (d : Nat) (x : α) :
    BinaryTree (α × σ) → BinaryTree (α × σ)
  | .nil => node ann .nil x .nil
  | .node (a, s) l r =>
      if x < a then balL ann d (insert ann d x l) a r
      else if a < x then balR ann d l a (insert ann d x r)
      else .node (a, s) l r

/-- Extract the original rightmost payload, with no default or order instance.
The optional pair contains the remaining tree first. -/
def splitMaxOption (ann : HeightAnnotation α σ) (d : Nat) :
    BinaryTree (α × σ) → Option (BinaryTree (α × σ) × α)
  | .nil => none
  | .node (a, _) l .nil => some (l, a)
  | .node (a, _) l (.node b rl rr) =>
      (splitMaxOption ann d (.node b rl rr)).map
        (fun p => (balL ann d l a p.1, p.2))

/-- Delete by left predecessor, using the opposite repair orientation after a
child shrinks. Returning an existing child retains its complete annotation. -/
def delete [LT α] [DecidableLT α] (ann : HeightAnnotation α σ) (d : Nat) (x : α) :
    BinaryTree (α × σ) → BinaryTree (α × σ)
  | .nil => .nil
  | .node (a, _) l r =>
      if x < a then balR ann d (delete ann d x l) a r
      else if a < x then balL ann d l a (delete ann d x r)
      else match splitMaxOption ann d l with
        | none => r
        | some (l', m) => balR ann d l' m r

@[simp] theorem insert_nil [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) :
    insert ann d x .nil = node ann .nil x .nil := rfl

theorem insert_node [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    insert ann d x (.node (a, s) l r) =
      if x < a then balL ann d (insert ann d x l) a r
      else if a < x then balR ann d l a (insert ann d x r)
      else .node (a, s) l r := rfl

theorem insert_of_lt [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hxa : x < a) :
    insert ann d x (.node (a, s) l r) = balL ann d (insert ann d x l) a r := by
  rw [insert_node, ite_eq_left hxa]

theorem insert_of_gt [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hxa : ¬ x < a) (hax : a < x) :
    insert ann d x (.node (a, s) l r) = balR ann d l a (insert ann d x r) := by
  rw [insert_node, ite_eq_right hxa, ite_eq_left hax]

theorem insert_of_not_lt_of_not_lt [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hxa : ¬ x < a) (hax : ¬ a < x) :
    insert ann d x (.node (a, s) l r) = .node (a, s) l r := by
  rw [insert_node, ite_eq_right hxa, ite_eq_right hax]

@[simp] theorem splitMaxOption_nil (ann : HeightAnnotation α σ) (d : Nat) :
    splitMaxOption ann d .nil = none := rfl

@[simp] theorem splitMaxOption_node_nil (ann : HeightAnnotation α σ) (d : Nat)
    (a : α) (s : σ) (l : BinaryTree (α × σ)) :
    splitMaxOption ann d (.node (a, s) l .nil) = some (l, a) := rfl

theorem splitMaxOption_node_of_ne_nil (ann : HeightAnnotation α σ) (d : Nat)
    (a : α) (s : σ) (l r : BinaryTree (α × σ)) (hr : r ≠ .nil) :
    splitMaxOption ann d (.node (a, s) l r) =
      (splitMaxOption ann d r).map (fun p => (balL ann d l a p.1, p.2)) := by
  cases r with
  | nil => exact (hr rfl).elim
  | node b rl rr => rfl

/-- Failure is exactly the empty input, for every payload type and tolerance. -/
theorem splitMaxOption_eq_none_iff (ann : HeightAnnotation α σ) (d : Nat)
    (t : BinaryTree (α × σ)) : splitMaxOption ann d t = none ↔ t = .nil := by
  induction t with
  | nil => simp only [splitMaxOption_nil]
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      by_cases hr : r = .nil
      · subst r
        simp only [splitMaxOption_node_nil, reduceCtorEq]
      · rw [splitMaxOption_node_of_ne_nil ann d a s l r hr]
        constructor
        · intro h
          cases hs : splitMaxOption ann d r with
          | none => exact (hr (ihr.mp hs)).elim
          | some p => simp only [hs, Option.map_some, reduceCtorEq] at h
        · intro h
          cases h

theorem splitMaxOption_exists_of_ne_nil (ann : HeightAnnotation α σ) (d : Nat)
    (t : BinaryTree (α × σ)) (ht : t ≠ .nil) :
    ∃ t' m, splitMaxOption ann d t = some (t', m) := by
  cases hs : splitMaxOption ann d t with
  | none => exact (ht ((splitMaxOption_eq_none_iff ann d t).mp hs)).elim
  | some p => exact ⟨p.1, p.2, rfl⟩

theorem splitMaxOption_node_of_some (ann : HeightAnnotation α σ) (d : Nat)
    (a : α) (s : σ) (l r r' : BinaryTree (α × σ)) (m : α)
    (hs : splitMaxOption ann d r = some (r', m)) :
    splitMaxOption ann d (.node (a, s) l r) = some (balL ann d l a r', m) := by
  have hr : r ≠ .nil := by
    intro h
    subst r
    simp only [splitMaxOption_nil, reduceCtorEq] at hs
  rw [splitMaxOption_node_of_ne_nil ann d a s l r hr, hs]
  rfl

@[simp] theorem delete_nil [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) :
    delete ann d x .nil = .nil := rfl

theorem delete_node [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    delete ann d x (.node (a, s) l r) =
      if x < a then balR ann d (delete ann d x l) a r
      else if a < x then balL ann d l a (delete ann d x r)
      else match splitMaxOption ann d l with
        | none => r
        | some (l', m) => balR ann d l' m r := rfl

theorem delete_of_lt [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hxa : x < a) :
    delete ann d x (.node (a, s) l r) = balR ann d (delete ann d x l) a r := by
  rw [delete_node, ite_eq_left hxa]

theorem delete_of_gt [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hxa : ¬ x < a) (hax : a < x) :
    delete ann d x (.node (a, s) l r) = balL ann d l a (delete ann d x r) := by
  rw [delete_node, ite_eq_right hxa, ite_eq_left hax]

theorem delete_of_not_lt_of_not_lt [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hxa : ¬ x < a) (hax : ¬ a < x) :
    delete ann d x (.node (a, s) l r) =
      match splitMaxOption ann d l with
        | none => r
        | some (l', m) => balR ann d l' m r := by
  rw [delete_node, ite_eq_right hxa, ite_eq_right hax]

/-- The extracted payload is rightmost, even on unordered, badly cached trees. -/
theorem inorder_splitMaxOption (ann : HeightAnnotation α σ) (d : Nat)
    (t t' : BinaryTree (α × σ)) (m : α)
    (hs : splitMaxOption ann d t = some (t', m)) :
    Trees.inorder (Cached.erase t') ++ [m] = Trees.inorder (Cached.erase t) := by
  revert hs
  induction t generalizing t' m with
  | nil =>
      intro hs
      simp only [splitMaxOption_nil, reduceCtorEq] at hs
  | node p l r ihl ihr =>
      intro hs
      rcases p with ⟨a, s⟩
      by_cases hr : r = .nil
      · subst r
        rw [splitMaxOption_node_nil] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        simp only [Cached.erase_node, Trees.inorder_node, Cached.erase_nil,
          Trees.inorder_nil]
      · obtain ⟨r', m', hrec⟩ := splitMaxOption_exists_of_ne_nil ann d r hr
        rw [splitMaxOption_node_of_some ann d a s l r r' m' hrec] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        have hI := ihr r' m' hrec
        simp only [inorder_balL, Cached.erase_node, Trees.inorder_node,
          List.append_assoc, List.cons_append]
        rw [hI]

theorem cacheValid_insert [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ))
    (hc : CacheValid ann t) : CacheValid ann (insert ann d x t) := by
  revert hc
  induction t with
  | nil =>
      intro _
      exact (node_cacheValid_iff ann .nil x .nil).mpr ⟨cacheValid_nil ann, cacheValid_nil ann⟩
  | node p l r ihl ihr =>
      intro hc
      rcases p with ⟨a, s⟩
      rcases (cacheValid_node ann a s l r).mp hc with ⟨hl, hr, _⟩
      rw [insert_node]
      split
      · exact cacheValid_balL ann d _ a r (ihl hl) hr
      · split
        · exact cacheValid_balR ann d l a _ hl (ihr hr)
        · exact hc

theorem cacheValid_splitMaxOption (ann : HeightAnnotation α σ) (d : Nat)
    (t t' : BinaryTree (α × σ)) (m : α)
    (hs : splitMaxOption ann d t = some (t', m)) (hc : CacheValid ann t) :
    CacheValid ann t' := by
  revert hs hc
  induction t generalizing t' m with
  | nil =>
      intro hs _
      simp only [splitMaxOption_nil, reduceCtorEq] at hs
  | node p l r ihl ihr =>
      intro hs hc
      rcases p with ⟨a, s⟩
      rcases (cacheValid_node ann a s l r).mp hc with ⟨hl, hr, _⟩
      by_cases he : r = .nil
      · subst r
        rw [splitMaxOption_node_nil] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        exact hl
      · obtain ⟨r', m', hrec⟩ := splitMaxOption_exists_of_ne_nil ann d r he
        rw [splitMaxOption_node_of_some ann d a s l r r' m' hrec] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        exact cacheValid_balL ann d l a r' hl (ihr r' m' hrec hr)

theorem cacheValid_delete [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ))
    (hc : CacheValid ann t) : CacheValid ann (delete ann d x t) := by
  revert hc
  induction t with
  | nil => intro _; exact cacheValid_nil ann
  | node p l r ihl ihr =>
      intro hc
      rcases p with ⟨a, s⟩
      rcases (cacheValid_node ann a s l r).mp hc with ⟨hl, hr, _⟩
      rw [delete_node]
      split
      · exact cacheValid_balR ann d _ a r (ihl hl) hr
      · split
        · exact cacheValid_balL ann d l a _ hl (ihr hr)
        · cases hs : splitMaxOption ann d l with
          | none => exact hr
          | some p =>
              rcases p with ⟨l', m⟩
              exact cacheValid_balR ann d l' m r
                (cacheValid_splitMaxOption ann d l l' m hs hl) hr

private theorem balL_growth (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (L : Nat)
    (hd : 1 ≤ d) (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlr : L ≤ r.height + d) (hrl : r.height ≤ L + d)
    (hg : l.height = L ∨ l.height = L + 1) :
    ValidD ann d (balL ann d l a r) ∧
      ((balL ann d l a r).height = max L r.height + 1 ∨
       (balL ann d l a r).height = (max L r.height + 1) + 1) := by
  refine ⟨validD_balL ann d l a r hd hl hr (by omega) (by omega), ?_⟩
  by_cases he : l.height = r.height + d + 1
  · have hh := height_balL_of_eq ann d l a r hd hl.2 hr.2 he
    omega
  · rw [height_balL_of_ne ann d l a r hl.2 hr.2 he]
    omega

private theorem balR_growth (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (R : Nat)
    (hd : 1 ≤ d) (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlr : l.height ≤ R + d) (hrl : R ≤ l.height + d)
    (hg : r.height = R ∨ r.height = R + 1) :
    ValidD ann d (balR ann d l a r) ∧
      ((balR ann d l a r).height = max l.height R + 1 ∨
       (balR ann d l a r).height = (max l.height R + 1) + 1) := by
  refine ⟨validD_balR ann d l a r hd hl hr (by omega) (by omega), ?_⟩
  by_cases he : r.height = l.height + d + 1
  · have hh := height_balR_of_eq ann d l a r hd hl.2 hr.2 he
    omega
  · rw [height_balR_of_ne ann d l a r hl.2 hr.2 he]
    omega

private theorem balL_shrink (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (R : Nat)
    (hd : 1 ≤ d) (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlr : l.height ≤ R + d) (hrl : R ≤ l.height + d)
    (hs : R = r.height ∨ R = r.height + 1) :
    ValidD ann d (balL ann d l a r) ∧
      (max l.height R + 1 = (balL ann d l a r).height ∨
       max l.height R + 1 = (balL ann d l a r).height + 1) := by
  refine ⟨validD_balL ann d l a r hd hl hr (by omega) (by omega), ?_⟩
  by_cases he : l.height = r.height + d + 1
  · have hh := height_balL_of_eq ann d l a r hd hl.2 hr.2 he
    omega
  · rw [height_balL_of_ne ann d l a r hl.2 hr.2 he]
    omega

private theorem balR_shrink (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (L : Nat)
    (hd : 1 ≤ d) (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlr : L ≤ r.height + d) (hrl : r.height ≤ L + d)
    (hs : L = l.height ∨ L = l.height + 1) :
    ValidD ann d (balR ann d l a r) ∧
      (max L r.height + 1 = (balR ann d l a r).height ∨
       max L r.height + 1 = (balR ann d l a r).height + 1) := by
  refine ⟨validD_balR ann d l a r hd hl hr (by omega) (by omega), ?_⟩
  by_cases he : r.height = l.height + d + 1
  · have hh := height_balR_of_eq ann d l a r hd hl.2 hr.2 he
    omega
  · rw [height_balR_of_ne ann d l a r hl.2 hr.2 he]
    omega

/-- Insertion preserves the complete invariant and grows actual height by0 or1,
for every positive tolerance and without an ordering-law assumption. -/
theorem validD_insert [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ))
    (hd : 1 ≤ d) (hv : ValidD ann d t) :
    ValidD ann d (insert ann d x t) ∧
      ((insert ann d x t).height = t.height ∨
       (insert ann d x t).height = t.height + 1) := by
  revert hv
  induction t with
  | nil =>
      intro _
      rw [insert_nil]
      refine ⟨(node_validD_iff ann d .nil x .nil).mpr
        ⟨validD_nil ann d, validD_nil ann d, ?_⟩, Or.inr rfl⟩
      exact (height_balance_iff d 0 0).mpr ⟨by omega, by omega⟩
  | node p l r ihl ihr =>
      intro hv
      rcases p with ⟨a, s⟩
      rcases (validD_node_iff ann d a s l r).mp hv with ⟨hl, hr, habs, _⟩
      have hb := (height_balance_iff d l.height r.height).mp habs
      rw [insert_node]
      split
      · have hi := ihl hl
        exact balL_growth ann d _ a r l.height hd hi.1 hr hb.1 hb.2 hi.2
      · split
        · have hi := ihr hr
          exact balR_growth ann d l a _ r.height hd hl hi.1 hb.1 hb.2 hi.2
        · exact ⟨hv, Or.inl rfl⟩

/-- Successful rightmost extraction preserves validity and loses at most one
actual level. The success equation exposes the nonempty input domain. -/
theorem validD_splitMaxOption (ann : HeightAnnotation α σ) (d : Nat)
    (t t' : BinaryTree (α × σ)) (m : α)
    (hs : splitMaxOption ann d t = some (t', m)) (hd : 1 ≤ d) (hv : ValidD ann d t) :
    ValidD ann d t' ∧ (t.height = t'.height ∨ t.height = t'.height + 1) := by
  revert hs hv
  induction t generalizing t' m with
  | nil =>
      intro hs _
      simp only [splitMaxOption_nil, reduceCtorEq] at hs
  | node p l r ihl ihr =>
      intro hs hv
      rcases p with ⟨a, s⟩
      rcases (validD_node_iff ann d a s l r).mp hv with ⟨hl, hr, habs, _⟩
      have hb := (height_balance_iff d l.height r.height).mp habs
      by_cases he : r = .nil
      · subst r
        rw [splitMaxOption_node_nil] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        exact ⟨hl, Or.inr (by simp only [BinaryTree.height, Nat.max_zero])⟩
      · obtain ⟨r', m', hrec⟩ := splitMaxOption_exists_of_ne_nil ann d r he
        rw [splitMaxOption_node_of_some ann d a s l r r' m' hrec] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        have hi := ihr r' m' hrec hr
        exact balL_shrink ann d l a r' r.height hd hl hi.1 hb.1 hb.2 hi.2

/-- Predecessor deletion preserves the complete invariant and loses0 or1 actual
levels, including the equal-child rotation ties that retain the old height. -/
theorem validD_delete [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ))
    (hd : 1 ≤ d) (hv : ValidD ann d t) :
    ValidD ann d (delete ann d x t) ∧
      (t.height = (delete ann d x t).height ∨
       t.height = (delete ann d x t).height + 1) := by
  revert hv
  induction t with
  | nil => intro _; exact ⟨validD_nil ann d, Or.inl rfl⟩
  | node p l r ihl ihr =>
      intro hv
      rcases p with ⟨a, s⟩
      rcases (validD_node_iff ann d a s l r).mp hv with ⟨hl, hr, habs, _⟩
      have hb := (height_balance_iff d l.height r.height).mp habs
      rw [delete_node]
      split
      · have hi := ihl hl
        exact balR_shrink ann d _ a r l.height hd hi.1 hr hb.1 hb.2 hi.2
      · split
        · have hi := ihr hr
          exact balL_shrink ann d l a _ r.height hd hl hi.1 hb.1 hb.2 hi.2
        · cases hs : splitMaxOption ann d l with
          | none =>
              have he := (splitMaxOption_eq_none_iff ann d l).mp hs
              subst l
              exact ⟨hr, Or.inr (by simp only [BinaryTree.height, Nat.zero_max])⟩
          | some p =>
              rcases p with ⟨l', m⟩
              have hi := validD_splitMaxOption ann d l l' m hs hd hl
              exact balR_shrink ann d l' m r l.height hd hi.1 hr hb.1 hb.2 hi.2

end Trees.HeightBalance
