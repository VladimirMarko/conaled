import Applications.Trees.HeightBalance.Rebalance
import Applications.Resources.TreeCache

/-!
# Measured local height-balance repair

The raw callbacks supply both values and observations. A height access charges
one cached-root read, and each repair charges one entry. The outer trigger
executes two additions and one equality; a reached inner test executes one
nonstrict comparison. Smart construction reuses `TreeCache.nodeRun`, including
its own single constructor charge, and consumes every returned inner tree.
Projections, pattern selection, pairing and observation arithmetic are free.
These declared source events do not measure runtime, allocation or bit work.
Correspondence and remaining update obligations: `docs/research/fdsa-height-updates.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.HeightBalance

universe u v
variable {α : Type u} {σ : Type v}

/-- Read the actual complete root summary before executing its height callback. -/
def htRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (t : BinaryTree (α × σ)) : Measured Nat Nat :=
  bind (TreeCache.readRun empty t) heightRun

theorem htRun_value (ann : Trees.HeightBalance.HeightAnnotation α σ)
    (heightRun : σ → Measured Nat Nat) (t : BinaryTree (α × σ))
    (hheight : ∀ s, (heightRun s).1 = ann.height s) :
    (htRun ann.empty heightRun t).1 = Trees.HeightBalance.ht ann t := by
  exact hheight _

theorem htRun_cost (empty : σ) (heightRun : σ → Measured Nat Nat)
    (t : BinaryTree (α × σ)) :
    (htRun empty heightRun t).2 =
      1 + (heightRun (Trees.Cached.read empty t)).2 := rfl

theorem htRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (t : BinaryTree (α × σ)) (H : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H) :
    (htRun empty heightRun t).2 ≤ 1 + H := by
  rw [htRun_cost]
  exact Nat.add_le_add_left (hH _) 1

/-- The two returned heights feed two distinct additions and then equality.
This helper adds no wrapper-entry charge. -/
def excessRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (d : Nat) (heavy other : BinaryTree (α × σ)) : Measured Bool Nat :=
  bind (htRun empty heightRun heavy) (fun heavyHeight =>
    bind (htRun empty heightRun other) (fun otherHeight =>
      bind (otherHeight + d, 1) (fun firstSum =>
        bind (firstSum + 1, 1) (fun threshold =>
          (decide (heavyHeight = threshold), 1)))))

theorem excessRun_value (empty : σ) (heightRun : σ → Measured Nat Nat)
    (d : Nat) (heavy other : BinaryTree (α × σ)) :
    (excessRun empty heightRun d heavy other).1 =
      decide ((htRun empty heightRun heavy).1 =
        (htRun empty heightRun other).1 + d + 1) := rfl

theorem excessRun_cost (empty : σ) (heightRun : σ → Measured Nat Nat)
    (d : Nat) (heavy other : BinaryTree (α × σ)) :
    (excessRun empty heightRun d heavy other).2 =
      (htRun empty heightRun heavy).2 + (htRun empty heightRun other).2 + 3 := by
  simp only [excessRun, bind]
  omega

theorem excessRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (d : Nat) (heavy other : BinaryTree (α × σ)) (H : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H) :
    (excessRun empty heightRun d heavy other).2 ≤ 5 + 2 * H := by
  rw [excessRun_cost]
  have hh := htRun_cost_le empty heightRun heavy H hH
  have ho := htRun_cost_le empty heightRun other H hH
  omega

/-- The inner nonstrict comparison includes equal-height deletion ties. -/
def leHeightRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (middle outer : BinaryTree (α × σ)) : Measured Bool Nat :=
  bind (htRun empty heightRun middle) (fun middleHeight =>
    bind (htRun empty heightRun outer) (fun outerHeight =>
      (decide (middleHeight ≤ outerHeight), 1)))

theorem leHeightRun_value (empty : σ) (heightRun : σ → Measured Nat Nat)
    (middle outer : BinaryTree (α × σ)) :
    (leHeightRun empty heightRun middle outer).1 =
      decide ((htRun empty heightRun middle).1 ≤
        (htRun empty heightRun outer).1) := rfl

theorem leHeightRun_cost (empty : σ) (heightRun : σ → Measured Nat Nat)
    (middle outer : BinaryTree (α × σ)) :
    (leHeightRun empty heightRun middle outer).2 =
      (htRun empty heightRun middle).2 + (htRun empty heightRun outer).2 + 1 := by
  simp only [leHeightRun, bind]
  omega

theorem leHeightRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (middle outer : BinaryTree (α × σ)) (H : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H) :
    (leHeightRun empty heightRun middle outer).2 ≤ 3 + 2 * H := by
  rw [leHeightRun_cost]
  have hm := htRun_cost_le empty heightRun middle H hH
  have ho := htRun_cost_le empty heightRun outer H hH
  omega

/-- Direct left repair, including both total fallback arms. -/
def balLRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    Measured (BinaryTree (α × σ)) Nat :=
  CallCount.tick (bind (excessRun empty heightRun d l r) (fun trigger =>
    if trigger then
      match l with
      | .nil => TreeCache.nodeRun empty combineRun l a r
      | .node (b, _) A B =>
          bind (leHeightRun empty heightRun B A) (fun single =>
            if single then
              bind (TreeCache.nodeRun empty combineRun B a r) (fun right =>
                TreeCache.nodeRun empty combineRun A b right)
            else
              match B with
              | .nil => TreeCache.nodeRun empty combineRun l a r
              | .node (c, _) B1 B2 =>
                  bind (TreeCache.nodeRun empty combineRun A b B1) (fun left =>
                    bind (TreeCache.nodeRun empty combineRun B2 a r) (fun right =>
                      TreeCache.nodeRun empty combineRun left c right)))
    else TreeCache.nodeRun empty combineRun l a r))

/-- Direct right repair; it does not assume a mirror law for the annotation. -/
def balRRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    Measured (BinaryTree (α × σ)) Nat :=
  CallCount.tick (bind (excessRun empty heightRun d r l) (fun trigger =>
    if trigger then
      match r with
      | .nil => TreeCache.nodeRun empty combineRun l a r
      | .node (c, _) B C =>
          bind (leHeightRun empty heightRun B C) (fun single =>
            if single then
              bind (TreeCache.nodeRun empty combineRun l a B) (fun left =>
                TreeCache.nodeRun empty combineRun left c C)
            else
              match B with
              | .nil => TreeCache.nodeRun empty combineRun l a r
              | .node (b, _) B1 B2 =>
                  bind (TreeCache.nodeRun empty combineRun l a B1) (fun left =>
                    bind (TreeCache.nodeRun empty combineRun B2 c C) (fun right =>
                      TreeCache.nodeRun empty combineRun left b right)))
    else TreeCache.nodeRun empty combineRun l a r))

/-- Raw erasure needs callback values, without cache, balance or order premises. -/
theorem balLRun_value (ann : Trees.HeightBalance.HeightAnnotation α σ)
    (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hheight : ∀ s, (heightRun s).1 = ann.height s)
    (hcombine : ∀ s x t, (combineRun s x t).1 = ann.combine s x t) :
    (balLRun ann.empty heightRun combineRun d l a r).1 =
      Trees.HeightBalance.balL ann d l a r := by
  have hh (t : BinaryTree (α × σ)) := htRun_value ann heightRun t hheight
  have hn (L : BinaryTree (α × σ)) (x : α) (R : BinaryTree (α × σ)) :
      (TreeCache.nodeRun ann.empty combineRun L x R).1 =
        Trees.HeightBalance.node ann L x R :=
    TreeCache.nodeRun_value ann.empty ann.combine combineRun L x R (hcombine _ _ _)
  unfold balLRun Trees.HeightBalance.balL
  simp only [CallCount.tick_value, bind_value, excessRun_value, hh, decide_eq_true_eq]
  split
  · cases l with
    | nil => exact hn .nil a r
    | node bs A B =>
        rcases bs with ⟨b, s⟩
        simp only [bind_value, leHeightRun_value, hh, decide_eq_true_eq]
        split
        · simp only [bind_value, hn]
        · cases B with
          | nil => exact hn (.node (b, s) A .nil) a r
          | node cs B1 B2 =>
              rcases cs with ⟨c, t⟩
              simp only [bind_value, hn]
  · exact hn l a r

theorem balRRun_value (ann : Trees.HeightBalance.HeightAnnotation α σ)
    (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ))
    (hheight : ∀ s, (heightRun s).1 = ann.height s)
    (hcombine : ∀ s x t, (combineRun s x t).1 = ann.combine s x t) :
    (balRRun ann.empty heightRun combineRun d l a r).1 =
      Trees.HeightBalance.balR ann d l a r := by
  have hh (t : BinaryTree (α × σ)) := htRun_value ann heightRun t hheight
  have hn (L : BinaryTree (α × σ)) (x : α) (R : BinaryTree (α × σ)) :
      (TreeCache.nodeRun ann.empty combineRun L x R).1 =
        Trees.HeightBalance.node ann L x R :=
    TreeCache.nodeRun_value ann.empty ann.combine combineRun L x R (hcombine _ _ _)
  unfold balRRun Trees.HeightBalance.balR
  simp only [CallCount.tick_value, bind_value, excessRun_value, hh, decide_eq_true_eq]
  split
  · cases r with
    | nil => exact hn l a .nil
    | node cs B C =>
        rcases cs with ⟨c, s⟩
        simp only [bind_value, leHeightRun_value, hh, decide_eq_true_eq]
        split
        · simp only [bind_value, hn]
        · cases B with
          | nil => exact hn l a (.node (c, s) .nil C)
          | node bs B1 B2 =>
              rcases bs with ⟨b, t⟩
              simp only [bind_value, hn]
  · exact hn l a r

/-- A bound on every reached callback, independent of its returned value.
The global combine premise also covers freshly constructed inner summaries. -/
theorem balLRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s x t, (combineRun s x t).2 ≤ K) :
    (balLRun empty heightRun combineRun d l a r).2 ≤ 18 + 4 * H + 3 * K := by
  have hn (L : BinaryTree (α × σ)) (x : α) (R : BinaryTree (α × σ)) :=
    TreeCache.nodeRun_le empty combineRun L x R K (hK _ _ _)
  have he := excessRun_cost_le empty heightRun d l r H hH
  unfold balLRun
  simp only [CallCount.tick_cost, bind]
  split
  · cases l with
    | nil =>
        have h := hn .nil a r
        simp only
        omega
    | node bs A B =>
        rcases bs with ⟨b, s⟩
        simp only
        have hi := leHeightRun_cost_le empty heightRun B A H hH
        split
        · have h1 := hn B a r
          have h2 := hn A b (TreeCache.nodeRun empty combineRun B a r).1
          omega
        · cases B with
          | nil =>
              have h := hn (.node (b, s) A .nil) a r
              simp only
              omega
          | node cs B1 B2 =>
              rcases cs with ⟨c, t⟩
              have h1 := hn A b B1
              have h2 := hn B2 a r
              have h3 := hn (TreeCache.nodeRun empty combineRun A b B1).1 c
                (TreeCache.nodeRun empty combineRun B2 a r).1
              simp only
              omega
  · have h := hn l a r
    omega

theorem balRRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s x t, (combineRun s x t).2 ≤ K) :
    (balRRun empty heightRun combineRun d l a r).2 ≤ 18 + 4 * H + 3 * K := by
  have hn (L : BinaryTree (α × σ)) (x : α) (R : BinaryTree (α × σ)) :=
    TreeCache.nodeRun_le empty combineRun L x R K (hK _ _ _)
  have he := excessRun_cost_le empty heightRun d r l H hH
  unfold balRRun
  simp only [CallCount.tick_cost, bind]
  split
  · cases r with
    | nil =>
        have h := hn l a .nil
        simp only
        omega
    | node cs B C =>
        rcases cs with ⟨c, s⟩
        simp only
        have hi := leHeightRun_cost_le empty heightRun B C H hH
        split
        · have h1 := hn l a B
          have h2 := hn (TreeCache.nodeRun empty combineRun l a B).1 c C
          omega
        · cases B with
          | nil =>
              have h := hn l a (.node (c, s) .nil C)
              simp only
              omega
          | node bs B1 B2 =>
              rcases bs with ⟨b, t⟩
              have h1 := hn l a B1
              have h2 := hn B2 c C
              have h3 := hn (TreeCache.nodeRun empty combineRun l a B1).1 b
                (TreeCache.nodeRun empty combineRun B2 c C).1
              simp only
              omega
  · have h := hn l a r
    omega

end Resources.HeightBalance
