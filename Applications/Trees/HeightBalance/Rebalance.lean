import Applications.Trees.HeightBalance.Basic

/-! Direct left and right local rotations for any positive height tolerance.
The raw programs read cached projections and recompute every new complete
annotation. Inorder and cache preservation are independent of balance; actual
height and full-validity laws state their additional assumptions separately.
Source and statement assessment: `docs/research/fdsa-height-rebalance.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.HeightBalance
universe u v
variable {α : Type u} {σ : Type v}

/-- Repair an exact left excess. The nonstrict inner test includes deletion ties.
The missing-pattern fallbacks make this raw program total without a default label. -/
def balL (ann : HeightAnnotation α σ) (d : Nat) (l : BinaryTree (α × σ))
    (a : α) (r : BinaryTree (α × σ)) : BinaryTree (α × σ) :=
  if ht ann l = ht ann r + d + 1 then
    match l with
    | .nil => node ann l a r
    | .node (b, _) A B =>
        if ht ann B ≤ ht ann A then
          node ann A b (node ann B a r)
        else
          match B with
          | .nil => node ann l a r
          | .node (c, _) B1 B2 => node ann (node ann A b B1) c (node ann B2 a r)
  else node ann l a r

/-- Directly oriented right repair; arbitrary annotations need not commute with mirror. -/
def balR (ann : HeightAnnotation α σ) (d : Nat) (l : BinaryTree (α × σ))
    (a : α) (r : BinaryTree (α × σ)) : BinaryTree (α × σ) :=
  if ht ann r = ht ann l + d + 1 then
    match r with
    | .nil => node ann l a r
    | .node (c, _) B C =>
        if ht ann B ≤ ht ann C then
          node ann (node ann l a B) c C
        else
          match B with
          | .nil => node ann l a r
          | .node (b, _) B1 B2 => node ann (node ann l a B1) b (node ann B2 c C)
  else node ann l a r

theorem left_ne_nil_of_trigger (ann : HeightAnnotation α σ) (d : Nat)
    (l r : BinaryTree (α × σ)) (h : ht ann l = ht ann r + d + 1) : l ≠ .nil := by
  intro he
  rw [he, ht_nil] at h
  omega

theorem right_ne_nil_of_trigger (ann : HeightAnnotation α σ) (d : Nat)
    (l r : BinaryTree (α × σ)) (h : ht ann r = ht ann l + d + 1) : r ≠ .nil :=
  left_ne_nil_of_trigger ann d r l h

theorem ne_nil_of_ht_lt (ann : HeightAnnotation α σ) (l r : BinaryTree (α × σ))
    (h : ht ann l < ht ann r) : r ≠ .nil := by
  intro he
  rw [he, ht_nil] at h
  omega

theorem balL_of_ne (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (h : ht ann l ≠ ht ann r + d + 1) : balL ann d l a r = node ann l a r := by
  rw [balL.eq_def, ite_eq_right h]

theorem balR_of_ne (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (h : ht ann r ≠ ht ann l + d + 1) : balR ann d l a r = node ann l a r := by
  rw [balR.eq_def, ite_eq_right h]

theorem balL_single (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (s : σ) (B : BinaryTree (α × σ))
    (c : α) (C : BinaryTree (α × σ))
    (h : ht ann (.node (a, s) A B) = ht ann C + d + 1)
    (side : ht ann B ≤ ht ann A) :
    balL ann d (.node (a, s) A B) c C = node ann A a (node ann B c C) := by
  rw [balL.eq_def, ite_eq_left h]
  dsimp only
  rw [ite_eq_left side]

theorem balL_double (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (s : σ) (B1 : BinaryTree (α × σ))
    (b : α) (t : σ) (B2 : BinaryTree (α × σ)) (c : α) (C : BinaryTree (α × σ))
    (h : ht ann (.node (a, s) A (.node (b, t) B1 B2)) = ht ann C + d + 1)
    (side : ht ann A < ht ann (.node (b, t) B1 B2)) :
    balL ann d (.node (a, s) A (.node (b, t) B1 B2)) c C =
      node ann (node ann A a B1) b (node ann B2 c C) := by
  rw [balL.eq_def, ite_eq_left h]
  dsimp only
  rw [ite_eq_right (Nat.not_le_of_lt side)]

theorem balR_single (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (B : BinaryTree (α × σ)) (c : α)
    (s : σ) (C : BinaryTree (α × σ))
    (h : ht ann (.node (c, s) B C) = ht ann A + d + 1)
    (side : ht ann B ≤ ht ann C) :
    balR ann d A a (.node (c, s) B C) = node ann (node ann A a B) c C := by
  rw [balR.eq_def, ite_eq_left h]
  dsimp only
  rw [ite_eq_left side]

theorem balR_double (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (B1 : BinaryTree (α × σ)) (b : α)
    (t : σ) (B2 : BinaryTree (α × σ)) (c : α) (s : σ) (C : BinaryTree (α × σ))
    (h : ht ann (.node (c, s) (.node (b, t) B1 B2) C) = ht ann A + d + 1)
    (side : ht ann C < ht ann (.node (b, t) B1 B2)) :
    balR ann d A a (.node (c, s) (.node (b, t) B1 B2) C) =
      node ann (node ann A a B1) b (node ann B2 c C) := by
  rw [balR.eq_def, ite_eq_left h]
  dsimp only
  rw [ite_eq_right (Nat.not_le_of_lt side)]

/-- Payload order and multiplicity survive even when the caches are malformed. -/
theorem inorder_balL (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    Trees.inorder (Cached.erase (balL ann d l a r)) =
      Trees.inorder (Cached.erase l) ++ (a :: Trees.inorder (Cached.erase r)) := by
  unfold balL
  split
  · cases l with
    | nil => exact inorder_node ann .nil a r
    | node bs A B =>
        rcases bs with ⟨b, s⟩
        dsimp only
        split
        · simp only [inorder_node, Cached.erase_node, Trees.inorder_node,
            List.append_assoc, List.cons_append]
        · cases B with
          | nil => exact inorder_node ann (.node (b, s) A .nil) a r
          | node cs B1 B2 =>
              rcases cs with ⟨c, t⟩
              simp only [inorder_node, Cached.erase_node, Trees.inorder_node,
                List.append_assoc, List.cons_append]
  · exact inorder_node ann l a r

theorem inorder_balR (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    Trees.inorder (Cached.erase (balR ann d l a r)) =
      Trees.inorder (Cached.erase l) ++ (a :: Trees.inorder (Cached.erase r)) := by
  unfold balR
  split
  · cases r with
    | nil => exact inorder_node ann l a .nil
    | node cs B C =>
        rcases cs with ⟨c, s⟩
        dsimp only
        split
        · simp only [inorder_node, Cached.erase_node, Trees.inorder_node,
            List.append_assoc, List.cons_append]
        · cases B with
          | nil => exact inorder_node ann l a (.node (c, s) .nil C)
          | node bs B1 B2 =>
              rcases bs with ⟨b, t⟩
              simp only [inorder_node, Cached.erase_node, Trees.inorder_node,
                List.append_assoc, List.cons_append]
  · exact inorder_node ann l a r

/-- All newly constructed summaries are correct; untouched children stay required. -/
theorem cacheValid_balL (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hl : CacheValid ann l) (hr : CacheValid ann r) : CacheValid ann (balL ann d l a r) := by
  unfold balL
  split
  · cases l with
    | nil => exact (node_cacheValid_iff ann .nil a r).mpr ⟨hl, hr⟩
    | node bs A B =>
        rcases bs with ⟨b, s⟩
        rcases (cacheValid_node ann b s A B).mp hl with ⟨hA, hB, _⟩
        dsimp only
        split
        · exact (node_cacheValid_iff ann A b _).mpr
            ⟨hA, (node_cacheValid_iff ann B a r).mpr ⟨hB, hr⟩⟩
        · cases B with
          | nil => exact (node_cacheValid_iff ann (.node (b, s) A .nil) a r).mpr ⟨hl, hr⟩
          | node cs B1 B2 =>
              rcases cs with ⟨c, t⟩
              rcases (cacheValid_node ann c t B1 B2).mp hB with ⟨hB1, hB2, _⟩
              exact (node_cacheValid_iff ann _ c _).mpr
                ⟨(node_cacheValid_iff ann A b B1).mpr ⟨hA, hB1⟩,
                  (node_cacheValid_iff ann B2 a r).mpr ⟨hB2, hr⟩⟩
  · exact (node_cacheValid_iff ann l a r).mpr ⟨hl, hr⟩

theorem cacheValid_balR (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hl : CacheValid ann l) (hr : CacheValid ann r) : CacheValid ann (balR ann d l a r) := by
  unfold balR
  split
  · cases r with
    | nil => exact (node_cacheValid_iff ann l a .nil).mpr ⟨hl, hr⟩
    | node cs B C =>
        rcases cs with ⟨c, s⟩
        rcases (cacheValid_node ann c s B C).mp hr with ⟨hB, hC, _⟩
        dsimp only
        split
        · exact (node_cacheValid_iff ann _ c C).mpr
            ⟨(node_cacheValid_iff ann l a B).mpr ⟨hl, hB⟩, hC⟩
        · cases B with
          | nil => exact (node_cacheValid_iff ann l a (.node (c, s) .nil C)).mpr ⟨hl, hr⟩
          | node bs B1 B2 =>
              rcases bs with ⟨b, t⟩
              rcases (cacheValid_node ann b t B1 B2).mp hB with ⟨hB1, hB2, _⟩
              exact (node_cacheValid_iff ann _ b _).mpr
                ⟨(node_cacheValid_iff ann l a B1).mpr ⟨hl, hB1⟩,
                  (node_cacheValid_iff ann B2 c C).mpr ⟨hB2, hC⟩⟩
  · exact (node_cacheValid_iff ann l a r).mpr ⟨hl, hr⟩

private theorem single_height (d x y k : Nat) (hd : 1 ≤ d)
    (hh : max x y + 1 = k + d + 1) (hs : y ≤ x) :
    max x (max y k + 1) + 1 = if y = x then k + d + 2 else k + d + 1 := by
  split <;> omega

private theorem double_height (d x p q k : Nat) (hd : 1 ≤ d)
    (hh : max x (max p q + 1) + 1 = k + d + 1) (hs : x < max p q + 1) :
    max (max x p + 1) (max q k + 1) + 1 = k + d + 1 := by
  omega

/-- The stronger double diagram needs heavy-child balance, but not balance of
the middle child's own children. Their balance is used later for full repair. -/
theorem double_rotation_height_bounds (d x p q k : Nat) (hd : 1 ≤ d)
    (hh : max x (max p q + 1) + 1 = k + d + 1)
    (hs : x < max p q + 1) (hb : max p q + 1 ≤ x + d) :
    max p q + 1 = k + d ∧ k ≤ x ∧ x + 1 ≤ k + d ∧
      k + 1 ≤ max x p + 1 ∧ max x p + 1 ≤ k + d ∧
      k + 1 ≤ max q k + 1 ∧ max q k + 1 ≤ k + d ∧
      max (max x p + 1) (max q k + 1) = k + d ∧
      max x p + 1 ≤ (max q k + 1) + (d - 1) ∧
      max q k + 1 ≤ (max x p + 1) + (d - 1) := by
  omega

private theorem single_balance (d x y k : Nat) (hd : 1 ≤ d)
    (hh : max x y + 1 = k + d + 1) (hs : y ≤ x) (hb : x ≤ y + d) :
    y ≤ k + d ∧ k ≤ y + d ∧
      x ≤ (max y k + 1) + d ∧ max y k + 1 ≤ x + d := by
  omega

private theorem double_balance (d x p q k : Nat) (hd : 1 ≤ d)
    (hh : max x (max p q + 1) + 1 = k + d + 1)
    (hs : x < max p q + 1) (hb : max p q + 1 ≤ x + d)
    (hpq : p ≤ q + d) (hqp : q ≤ p + d) :
    x ≤ p + d ∧ p ≤ x + d ∧ q ≤ k + d ∧ k ≤ q + d ∧
      max x p + 1 ≤ (max q k + 1) + d ∧
      max q k + 1 ≤ (max x p + 1) + d := by
  omega

theorem height_balL_of_ne (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hl : CacheValid ann l) (hr : CacheValid ann r)
    (h : l.height ≠ r.height + d + 1) :
    (balL ann d l a r).height = max l.height r.height + 1 := by
  have hn : ht ann l ≠ ht ann r + d + 1 := by
    rw [ht_eq_height_of_cacheValid ann l hl, ht_eq_height_of_cacheValid ann r hr]
    exact h
  rw [balL_of_ne ann d l a r hn, height_node]

theorem height_balR_of_ne (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hl : CacheValid ann l) (hr : CacheValid ann r)
    (h : r.height ≠ l.height + d + 1) :
    (balR ann d l a r).height = max l.height r.height + 1 := by
  have hn : ht ann r ≠ ht ann l + d + 1 := by
    rw [ht_eq_height_of_cacheValid ann l hl, ht_eq_height_of_cacheValid ann r hr]
    exact h
  rw [balR_of_ne ann d l a r hn, height_node]

/-- An equal-height single rotation has the higher result, even with only cache
correctness available. Recursive child balance is not needed for this equation. -/
theorem height_balL_single (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (s : σ) (B : BinaryTree (α × σ))
    (c : α) (C : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : CacheValid ann (.node (a, s) A B)) (hr : CacheValid ann C)
    (h : (BinaryTree.node (a, s) A B).height = C.height + d + 1)
    (side : ht ann B ≤ ht ann A) :
    (balL ann d (.node (a, s) A B) c C).height =
      if B.height = A.height then C.height + d + 2 else C.height + d + 1 := by
  have hraw : ht ann (.node (a, s) A B) = ht ann C + d + 1 := by
    rw [ht_eq_height_of_cacheValid ann _ hl, ht_eq_height_of_cacheValid ann _ hr]
    exact h
  rcases (cacheValid_node ann a s A B).mp hl with ⟨hA, hB, _⟩
  have hs : B.height ≤ A.height := by
    simpa only [ht_eq_height_of_cacheValid ann A hA,
      ht_eq_height_of_cacheValid ann B hB] using side
  rw [balL_single ann d A a s B c C hraw side, height_node, height_node]
  exact single_height d A.height B.height C.height hd h hs

theorem height_balR_single (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (B : BinaryTree (α × σ)) (c : α)
    (s : σ) (C : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : CacheValid ann A) (hr : CacheValid ann (.node (c, s) B C))
    (h : (BinaryTree.node (c, s) B C).height = A.height + d + 1)
    (side : ht ann B ≤ ht ann C) :
    (balR ann d A a (.node (c, s) B C)).height =
      if B.height = C.height then A.height + d + 2 else A.height + d + 1 := by
  have hraw : ht ann (.node (c, s) B C) = ht ann A + d + 1 := by
    rw [ht_eq_height_of_cacheValid ann _ hl, ht_eq_height_of_cacheValid ann _ hr]
    exact h
  rcases (cacheValid_node ann c s B C).mp hr with ⟨hB, hC, _⟩
  have hs : B.height ≤ C.height := by
    simpa only [ht_eq_height_of_cacheValid ann B hB,
      ht_eq_height_of_cacheValid ann C hC] using side
  rw [balR_single ann d A a B c s C hraw side, height_node, height_node]
  have hh : max C.height B.height + 1 = A.height + d + 1 := by
    simpa only [BinaryTree.height, Nat.max_comm] using h
  simpa only [Nat.max_comm] using single_height d C.height B.height A.height hd hh hs

theorem height_balL_double (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (s : σ) (B : BinaryTree (α × σ))
    (c : α) (C : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : CacheValid ann (.node (a, s) A B)) (hr : CacheValid ann C)
    (h : (BinaryTree.node (a, s) A B).height = C.height + d + 1)
    (side : ht ann A < ht ann B) :
    (balL ann d (.node (a, s) A B) c C).height = C.height + d + 1 := by
  have hraw : ht ann (.node (a, s) A B) = ht ann C + d + 1 := by
    rw [ht_eq_height_of_cacheValid ann _ hl, ht_eq_height_of_cacheValid ann _ hr]
    exact h
  rcases (cacheValid_node ann a s A B).mp hl with ⟨hA, hB, _⟩
  have hs : A.height < B.height := by
    simpa only [ht_eq_height_of_cacheValid ann A hA,
      ht_eq_height_of_cacheValid ann B hB] using side
  cases B with
  | nil => simp only [BinaryTree.height] at hs; omega
  | node bs B1 B2 =>
      rcases bs with ⟨b, t⟩
      rw [balL_double ann d A a s B1 b t B2 c C hraw side,
        height_node, height_node, height_node]
      exact double_height d A.height B1.height B2.height C.height hd h hs

theorem height_balR_double (ann : HeightAnnotation α σ) (d : Nat)
    (A : BinaryTree (α × σ)) (a : α) (B : BinaryTree (α × σ)) (c : α)
    (s : σ) (C : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : CacheValid ann A) (hr : CacheValid ann (.node (c, s) B C))
    (h : (BinaryTree.node (c, s) B C).height = A.height + d + 1)
    (side : ht ann C < ht ann B) :
    (balR ann d A a (.node (c, s) B C)).height = A.height + d + 1 := by
  have hraw : ht ann (.node (c, s) B C) = ht ann A + d + 1 := by
    rw [ht_eq_height_of_cacheValid ann _ hl, ht_eq_height_of_cacheValid ann _ hr]
    exact h
  rcases (cacheValid_node ann c s B C).mp hr with ⟨hB, hC, _⟩
  have hs : C.height < B.height := by
    simpa only [ht_eq_height_of_cacheValid ann B hB,
      ht_eq_height_of_cacheValid ann C hC] using side
  cases B with
  | nil => simp only [BinaryTree.height] at hs; omega
  | node bs B1 B2 =>
      rcases bs with ⟨b, t⟩
      rw [balR_double ann d A a B1 b t B2 c s C hraw side,
        height_node, height_node, height_node]
      have hh : max C.height (max B2.height B1.height + 1) + 1 = A.height + d + 1 := by
        simpa only [BinaryTree.height, Nat.max_comm] using h
      have hs' : C.height < max B2.height B1.height + 1 := by
        simpa only [BinaryTree.height, Nat.max_comm] using hs
      simpa only [Nat.max_comm] using
        double_height d C.height B2.height B1.height A.height hd hh hs'

theorem height_balL_of_eq (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : CacheValid ann l) (hr : CacheValid ann r)
    (h : l.height = r.height + d + 1) :
    (balL ann d l a r).height = r.height + d + 1 ∨
      (balL ann d l a r).height = r.height + d + 2 := by
  cases l with
  | nil => simp only [BinaryTree.height] at h; omega
  | node bs A B =>
      rcases bs with ⟨b, s⟩
      by_cases hs : ht ann B ≤ ht ann A
      · rw [height_balL_single ann d A b s B a r hd hl hr h hs]
        split <;> omega
      · exact Or.inl (height_balL_double ann d A b s B a r hd hl hr h (Nat.lt_of_not_ge hs))

theorem height_balR_of_eq (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : CacheValid ann l) (hr : CacheValid ann r)
    (h : r.height = l.height + d + 1) :
    (balR ann d l a r).height = l.height + d + 1 ∨
      (balR ann d l a r).height = l.height + d + 2 := by
  cases r with
  | nil => simp only [BinaryTree.height] at h; omega
  | node cs B C =>
      rcases cs with ⟨c, s⟩
      by_cases hs : ht ann B ≤ ht ann C
      · rw [height_balR_single ann d l a B c s C hd hl hr h hs]
        split <;> omega
      · exact Or.inl (height_balR_double ann d l a B c s C hd hl hr h (Nat.lt_of_not_ge hs))

private theorem validD_node_of_le (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlr : l.height ≤ r.height + d) (hrl : r.height ≤ l.height + d) :
    ValidD ann d (node ann l a r) :=
  (node_validD_iff ann d l a r).mpr ⟨hl, hr, (height_balance_iff d _ _).mpr ⟨hlr, hrl⟩⟩

/-- Repair over the full one-sided left range, including its extra imbalance level. -/
theorem validD_balL (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlo : r.height - d ≤ l.height) (hhi : l.height ≤ r.height + d + 1) :
    ValidD ann d (balL ann d l a r) := by
  by_cases he : l.height = r.height + d + 1
  · have hraw : ht ann l = ht ann r + d + 1 := by
      rw [ht_eq_height ann d l hl, ht_eq_height ann d r hr]
      exact he
    cases l with
    | nil => simp only [BinaryTree.height] at he; omega
    | node bs A B =>
        rcases bs with ⟨b, s⟩
        rcases (validD_node_iff ann d b s A B).mp hl with ⟨hA, hB, habs, _⟩
        have hab := (height_balance_iff d A.height B.height).mp habs
        by_cases side : ht ann B ≤ ht ann A
        · have hs : B.height ≤ A.height := by
            simpa only [ht_eq_height ann d A hA, ht_eq_height ann d B hB] using side
          have hm := single_balance d A.height B.height r.height hd he hs hab.1
          rw [balL_single ann d A b s B a r hraw side]
          have hBr := validD_node_of_le ann d B a r hB hr hm.1 hm.2.1
          apply validD_node_of_le ann d A b (node ann B a r) hA hBr
          · simpa only [height_node] using hm.2.2.1
          · simpa only [height_node] using hm.2.2.2
        · have side' : ht ann A < ht ann B := Nat.lt_of_not_ge side
          have hs : A.height < B.height := by
            simpa only [ht_eq_height ann d A hA, ht_eq_height ann d B hB] using side'
          cases B with
          | nil => simp only [BinaryTree.height] at hs; omega
          | node cs B1 B2 =>
              rcases cs with ⟨c, t⟩
              rcases (validD_node_iff ann d c t B1 B2).mp hB with ⟨hB1, hB2, hmid, _⟩
              have hpair := (height_balance_iff d B1.height B2.height).mp hmid
              have hm := double_balance d A.height B1.height B2.height r.height
                hd he hs hab.2 hpair.1 hpair.2
              rw [balL_double ann d A b s B1 c t B2 a r hraw side']
              have hleft := validD_node_of_le ann d A b B1 hA hB1 hm.1 hm.2.1
              have hright := validD_node_of_le ann d B2 a r hB2 hr hm.2.2.1 hm.2.2.2.1
              apply validD_node_of_le ann d _ c _ hleft hright
              · simpa only [height_node] using hm.2.2.2.2.1
              · simpa only [height_node] using hm.2.2.2.2.2
  · have hraw : ht ann l ≠ ht ann r + d + 1 := by
      rw [ht_eq_height ann d l hl, ht_eq_height ann d r hr]
      exact he
    rw [balL_of_ne ann d l a r hraw]
    apply validD_node_of_le ann d l a r hl hr
    · omega
    · exact (height_lower_bound_iff d l.height r.height).mp hlo

/-- The independently oriented repair over the full one-sided right range. -/
theorem validD_balR (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (hd : 1 ≤ d)
    (hl : ValidD ann d l) (hr : ValidD ann d r)
    (hlo : l.height - d ≤ r.height) (hhi : r.height ≤ l.height + d + 1) :
    ValidD ann d (balR ann d l a r) := by
  by_cases he : r.height = l.height + d + 1
  · have hraw : ht ann r = ht ann l + d + 1 := by
      rw [ht_eq_height ann d l hl, ht_eq_height ann d r hr]
      exact he
    cases r with
    | nil => simp only [BinaryTree.height] at he; omega
    | node cs B C =>
        rcases cs with ⟨c, s⟩
        rcases (validD_node_iff ann d c s B C).mp hr with ⟨hB, hC, habs, _⟩
        have hbc := (height_balance_iff d B.height C.height).mp habs
        by_cases side : ht ann B ≤ ht ann C
        · have hs : B.height ≤ C.height := by
            simpa only [ht_eq_height ann d B hB, ht_eq_height ann d C hC] using side
          have hh : max C.height B.height + 1 = l.height + d + 1 := by
            simpa only [BinaryTree.height, Nat.max_comm] using he
          have hm := single_balance d C.height B.height l.height hd hh hs hbc.2
          rw [balR_single ann d l a B c s C hraw side]
          have hlB := validD_node_of_le ann d l a B hl hB hm.2.1 hm.1
          apply validD_node_of_le ann d (node ann l a B) c C hlB hC
          · simpa only [height_node, Nat.max_comm] using hm.2.2.2
          · simpa only [height_node, Nat.max_comm] using hm.2.2.1
        · have side' : ht ann C < ht ann B := Nat.lt_of_not_ge side
          have hs : C.height < B.height := by
            simpa only [ht_eq_height ann d B hB, ht_eq_height ann d C hC] using side'
          cases B with
          | nil => simp only [BinaryTree.height] at hs; omega
          | node bs B1 B2 =>
              rcases bs with ⟨b, t⟩
              rcases (validD_node_iff ann d b t B1 B2).mp hB with ⟨hB1, hB2, hmid, _⟩
              have hpair := (height_balance_iff d B1.height B2.height).mp hmid
              have hh : max C.height (max B2.height B1.height + 1) + 1 = l.height + d + 1 := by
                simpa only [BinaryTree.height, Nat.max_comm] using he
              have hs' : C.height < max B2.height B1.height + 1 := by
                simpa only [BinaryTree.height, Nat.max_comm] using hs
              have hb : max B2.height B1.height + 1 ≤ C.height + d := by
                simpa only [BinaryTree.height, Nat.max_comm] using hbc.1
              have hm := double_balance d C.height B2.height B1.height l.height
                hd hh hs' hb hpair.2 hpair.1
              rw [balR_double ann d l a B1 b t B2 c s C hraw side']
              have hleft := validD_node_of_le ann d l a B1 hl hB1 hm.2.2.2.1 hm.2.2.1
              have hright := validD_node_of_le ann d B2 c C hB2 hC hm.2.1 hm.1
              apply validD_node_of_le ann d _ b _ hleft hright
              · simpa only [height_node, Nat.max_comm] using hm.2.2.2.2.2
              · simpa only [height_node, Nat.max_comm] using hm.2.2.2.2.1
  · have hraw : ht ann r ≠ ht ann l + d + 1 := by
      rw [ht_eq_height ann d l hl, ht_eq_height ann d r hr]
      exact he
    rw [balR_of_ne ann d l a r hraw]
    apply validD_node_of_le ann d l a r hl hr
    · exact (height_lower_bound_iff d r.height l.height).mp hlo
    · omega

end Trees.HeightBalance
