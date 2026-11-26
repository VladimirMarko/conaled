import Applications.Search.IntervalTree.Balanced
import Applications.Resources.TreeCache

/-!
# Measured direct interval queries

Each search invocation costs one, including nil. A reached nonempty node executes
one measured interval projection and a short-circuit overlap test. A root hit
stops immediately. On a miss, an empty left child is bypassed; otherwise one
cached maximum read and the actual measured pruning result select one original
child. The maximum-only tree is a proof observation, never an executed traversal.
Projection and comparison callbacks contribute their actual observations. Pairing,
pattern selection and observation bookkeeping cost zero. These declared source
events give no runtime, allocation or bit-complexity guarantee.
Correspondence: `docs/research/fdsa-measured-rectangle-scan.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.IntervalTree

universe u v
variable {α : Type u} {κ : Type v}

section Overlap
variable [LE α]

/-- The first returned comparison controls whether the second executes.
There is no extra entry charge for this helper. -/
def overlapRun (leRun : α → α → Measured Bool Nat)
    (query stored : Search.IntervalKey α) : Measured Bool Nat :=
  bind (leRun stored.low query.high) (fun first =>
    if first then leRun query.low stored.high else pure false)

theorem overlapRun_of_first_false (leRun : α → α → Measured Bool Nat)
    (query stored : Search.IntervalKey α)
    (first : (leRun stored.low query.high).1 = false) :
    overlapRun leRun query stored = (false, (leRun stored.low query.high).2) := by
  simp [overlapRun, bind, pure, first]

theorem overlapRun_of_first_true (leRun : α → α → Measured Bool Nat)
    (query stored : Search.IntervalKey α)
    (first : (leRun stored.low query.high).1 = true) :
    overlapRun leRun query stored =
      ((leRun query.low stored.high).1,
        (leRun stored.low query.high).2 + (leRun query.low stored.high).2) := by
  simp [overlapRun, bind, first]

theorem overlapRun_value [DecidableLE α] (leRun : α → α → Measured Bool Nat)
    (query stored : Search.IntervalKey α)
    (hle : ∀ x y, (leRun x y).1 = decide (x ≤ y)) :
    (overlapRun leRun query stored).1 = decide (Search.IntervalKey.Overlap query stored) := by
  by_cases first : stored.low ≤ query.high <;>
    simp [overlapRun, bind, pure, hle, Search.IntervalKey.Overlap, first]

/-- This equation retains the actual first cost and only the reached second cost. -/
theorem overlapRun_cost (leRun : α → α → Measured Bool Nat)
    (query stored : Search.IntervalKey α) :
    (overlapRun leRun query stored).2 = (leRun stored.low query.high).2 +
      (if (leRun stored.low query.high).1 then (leRun query.low stored.high).2 else 0) := by
  cases first : (leRun stored.low query.high).1 <;>
    simp [overlapRun, bind, pure, first]

theorem overlapRun_cost_le (leRun : α → α → Measured Bool Nat)
    (query stored : Search.IntervalKey α) (E : Nat)
    (hE : ∀ x y, (leRun x y).2 ≤ E) :
    (overlapRun leRun query stored).2 ≤ 2 * E := by
  rw [overlapRun_cost]
  have hfirst := hE stored.low query.high
  have hsecond := hE query.low stored.high
  split <;> omega

end Overlap

section Maximum
variable [Bot α]

/-- One actual cached-root read, followed by a free maximum projection. -/
def maxHiRun (t : BinaryTree (κ × (Nat × α))) : Measured α Nat :=
  bind (TreeCache.readRun (0, ⊥) t) (fun summary => pure summary.2)

@[simp] theorem maxHiRun_value (t : BinaryTree (κ × (Nat × α))) :
    (maxHiRun t).1 = Search.IntervalTree.Balanced.maxHi t := rfl

@[simp] theorem maxHiRun_cost (t : BinaryTree (κ × (Nat × α))) :
    (maxHiRun t).2 = 1 := rfl

end Maximum

section Search
variable [LE α] [Bot α]

/-- Execute projection, overlap and pruning on their actual returned values. -/
def searchRun (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat) :
    BinaryTree (κ × (Nat × α)) → Search.IntervalKey α → Measured Bool Nat
  | .nil, _ => (false, 1)
  | .node (a, _) l r, query =>
      CallCount.tick (bind (ivRun a) (fun stored =>
        bind (overlapRun leRun query stored) (fun hit =>
          if hit then pure true
          else match l with
            | .nil => searchRun ivRun leRun r query
            | .node _ _ _ =>
                bind (maxHiRun l) (fun maximum =>
                  bind (leRun query.low maximum) (fun takeLeft =>
                    if takeLeft then searchRun ivRun leRun l query
                    else searchRun ivRun leRun r query)))))

@[simp] theorem searchRun_nil (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat) (query : Search.IntervalKey α) :
    searchRun ivRun leRun .nil query = (false, 1) := rfl

theorem searchRun_node (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat) (a : κ) (summary : Nat × α)
    (l r : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α) :
    searchRun ivRun leRun (.node (a, summary) l r) query =
      CallCount.tick (bind (ivRun a) (fun stored =>
        bind (overlapRun leRun query stored) (fun hit =>
          if hit then pure true
          else match l with
            | .nil => searchRun ivRun leRun r query
            | .node _ _ _ =>
                bind (maxHiRun l) (fun maximum =>
                  bind (leRun query.low maximum) (fun takeLeft =>
                    if takeLeft then searchRun ivRun leRun l query
                    else searchRun ivRun leRun r query))))) := rfl

/-- Raw erasure does not assume truthful heights, valid maxima, order or balance. -/
theorem searchRun_value [DecidableLE α] (iv : κ → Search.IntervalKey α)
    (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α)
    (hiv : ∀ a, (ivRun a).1 = iv a)
    (hle : ∀ x y, (leRun x y).1 = decide (x ≤ y)) :
    (searchRun ivRun leRun t query).1 = Search.IntervalTree.Balanced.search iv t query := by
  induction t with
  | nil => rfl
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, summary⟩
      rw [searchRun_node, Search.IntervalTree.Balanced.search.eq_def]
      simp only [CallCount.tick_value, bind_value, hiv,
        overlapRun_value leRun query (iv a) hle, decide_eq_true_eq]
      split
      · rfl
      · cases l with
        | nil => exact ihr
        | node binding ll lr =>
            simp only [bind_value, maxHiRun_value, hle, decide_eq_true_eq]
            split
            · exact ihl
            · exact ihr

/-- Every reached node adds at most one projection, three comparisons and two
local charges. Only one original child is selected. No value-erasure or tree
invariant premise is needed for this structural cost bound. -/
theorem searchRun_cost_le (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α) (P E : Nat)
    (hP : ∀ a, (ivRun a).2 ≤ P)
    (hE : ∀ x y, (leRun x y).2 ≤ E) :
    (searchRun ivRun leRun t query).2 ≤ (P + 3 * E + 2) * t.height + 1 := by
  induction t with
  | nil => simp only [searchRun_nil, BinaryTree.height, Nat.mul_zero, Nat.zero_add, le_refl]
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, summary⟩
      have hproj := hP a
      have hover := overlapRun_cost_le leRun query (ivRun a).1 E hE
      have hleft := ihl.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left (P + 3 * E + 2) (Nat.le_max_left l.height r.height)) 1)
      have hright := ihr.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left (P + 3 * E + 2) (Nat.le_max_right l.height r.height)) 1)
      rw [searchRun_node]
      simp only [CallCount.tick_cost, bind, pure, BinaryTree.height, Nat.mul_add, Nat.mul_one]
      split
      · omega
      · cases l with
        | nil =>
            simp only
            omega
        | node binding ll lr =>
            have hprune := hE query.low (maxHiRun (.node binding ll lr)).1
            simp only [maxHiRun_cost]
            split <;> omega

/-- Measured success inherits the raw original-key witness through erasure. -/
theorem searchRun_sound [DecidableLE α] (iv : κ → Search.IntervalKey α)
    (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α)
    (hiv : ∀ a, (ivRun a).1 = iv a)
    (hle : ∀ x y, (leRun x y).1 = decide (x ≤ y))
    (found : (searchRun ivRun leRun t query).1 = true) :
    ∃ a ∈ Trees.setTree (Trees.Cached.erase t), Search.IntervalKey.Overlap (iv a) query := by
  rw [searchRun_value iv ivRun leRun t query hiv hle] at found
  exact Search.IntervalTree.Balanced.search_sound iv found

end Search

section Correctness
variable [LinearOrder α] [OrderBot α]

/-- Valid maxima and weak low order suffice; stored heights and balance are absent. -/
theorem searchRun_correct (iv : κ → Search.IntervalKey α)
    (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α)
    (hiv : ∀ a, (ivRun a).1 = iv a)
    (hle : ∀ x y, (leRun x y).1 = decide (x ≤ y))
    (valid : Search.IntervalTree.CacheValid iv (Search.IntervalTree.Balanced.maximumTree t))
    (ordered : (Trees.inorder (Trees.Cached.erase t)).Pairwise
      (fun a b => (iv a).low ≤ (iv b).low)) :
    (searchRun ivRun leRun t query).1 = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), Search.IntervalKey.Overlap (iv a) query := by
  rw [searchRun_value iv ivRun leRun t query hiv hle]
  exact Search.IntervalTree.Balanced.search_correct iv valid ordered query

theorem searchRun_correct_of_strict [LT κ] (iv : κ → Search.IntervalKey α)
    (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α)
    (hiv : ∀ a, (ivRun a).1 = iv a)
    (hle : ∀ x y, (leRun x y).1 = decide (x ≤ y))
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low)
    (valid : Search.IntervalTree.CacheValid iv (Search.IntervalTree.Balanced.maximumTree t))
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) :
    (searchRun ivRun leRun t query).1 = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), Search.IntervalKey.Overlap (iv a) query := by
  rw [searchRun_value iv ivRun leRun t query hiv hle]
  exact Search.IntervalTree.Balanced.search_correct_of_strict iv compatible valid strict query

end Correctness
end Resources.IntervalTree
