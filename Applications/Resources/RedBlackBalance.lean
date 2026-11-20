import Applications.Resources.Measured
import Applications.Search.RedBlack.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Measured source balancing

The metric vector records explicit source observations. Each red-red attempt
starts afresh and stops at the first wrong node constructor or color. Its
returned decomposition supplies the constructed rotation. These counts do not
describe generated matcher instructions, physical allocation or sharing.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

open Search.RedBlack (Tree)

/-- Independent observations used by the source operation executions. -/
inductive Metric where
  | visits
  | comparisons
  | comparatorWork
  | balanceCalls
  | patternAttempts
  | datatypeObservations
  | nodeConstructions
  | terminalNils
  | rootInspections
  | enumerationCalls
  | consConstructions
  deriving DecidableEq

instance : Fintype Metric where
  elems := {.visits, .comparisons, .comparatorWork, .balanceCalls,
    .patternAttempts, .datatypeObservations, .nodeConstructions,
    .terminalNils, .rootInspections, .enumerationCalls, .consConstructions}
  complete metric := by cases metric <;> simp

/-- Addition and order are pointwise; no metric is hidden in a tuple position. -/
abbrev Cost := Metric → Nat

/-- Charge one named observation with the stated multiplicity. -/
def tick (metric : Metric) (n : Nat) : Cost :=
  fun observed => if observed = metric then n else 0

@[simp] theorem tick_same (metric : Metric) (n : Nat) : tick metric n metric = n := by
  simp [tick]

@[simp] theorem tick_other (metric observed : Metric) (n : Nat)
    (different : observed ≠ metric) : tick metric n observed = 0 := by
  simp [tick, different]

@[simp] theorem tick_zero (metric : Metric) : tick metric 0 = 0 := by
  funext observed
  simp [tick]

theorem tick_add (metric : Metric) (m n : Nat) :
    tick metric (m + n) = tick metric m + tick metric n := by
  funext observed
  by_cases h : observed = metric <;> simp [tick, h]

/-- Construct the actual source node, charging one syntactic construction. -/
def nodeRun (color : RBTree.RBColor) (left : Tree κ ν) (binding : κ × ν)
    (right : Tree κ ν) : Measured (Tree κ ν) Cost :=
  (.node color left binding right, tick .nodeConstructions 1)

@[simp] theorem nodeRun_value (color : RBTree.RBColor) (left : Tree κ ν)
    (binding : κ × ν) (right : Tree κ ν) :
    (nodeRun color left binding right).1 = .node color left binding right := rfl

@[simp] theorem nodeRun_cost (color : RBTree.RBColor) (left : Tree κ ν)
    (binding : κ × ν) (right : Tree κ ν) :
    (nodeRun color left binding right).2 = tick .nodeConstructions 1 := rfl

/-- The fields returned by a successful red-node observation. -/
structure RedView (κ : Type u) (ν : Type v) where
  left : Tree κ ν
  binding : κ × ν
  right : Tree κ ν

/-- Inspect the node constructor and, only for a node, its color. -/
def redNodeRun (t : Tree κ ν) : Measured (Option (RedView κ ν)) Cost :=
  bind (t, tick .datatypeObservations 1) fun
    | .nil => pure none
    | .node color left binding right =>
        bind (color, tick .datatypeObservations 1) fun
          | .red => pure (some ⟨left, binding, right⟩)
          | .black => pure none

/-- The actual two red-node decomposition, ordered by its in-order labels. -/
structure RedPair (κ : Type u) (ν : Type v) where
  first : Tree κ ν
  lower : κ × ν
  middle : Tree κ ν
  upper : κ × ν
  last : Tree κ ν

/-- One fresh complete left-red-child attempt. -/
def leftPairRun (t : Tree κ ν) : Measured (Option (RedPair κ ν)) Cost :=
  bind ((), tick .patternAttempts 1) fun _ =>
    bind (redNodeRun t) fun
      | none => pure none
      | some outer =>
          bind (redNodeRun outer.left) fun
            | none => pure none
            | some inner =>
                pure (some ⟨inner.left, inner.binding, inner.right,
                  outer.binding, outer.right⟩)

/-- One fresh complete right-red-child attempt. -/
def rightPairRun (t : Tree κ ν) : Measured (Option (RedPair κ ν)) Cost :=
  bind ((), tick .patternAttempts 1) fun _ =>
    bind (redNodeRun t) fun
      | none => pure none
      | some outer =>
          bind (redNodeRun outer.right) fun
            | none => pure none
            | some inner =>
                pure (some ⟨outer.left, outer.binding, inner.left,
                  inner.binding, inner.right⟩)

/-- Construct the three nodes returned by a selected left-side pattern. -/
def rotateLeftRun (parts : RedPair κ ν) (binding : κ × ν) (right : Tree κ ν) :
    Measured (Tree κ ν) Cost :=
  bind (nodeRun .black parts.first parts.lower parts.middle) fun left =>
    bind (nodeRun .black parts.last binding right) fun right =>
      nodeRun .red left parts.upper right

/-- Construct the three nodes returned by a selected right-side pattern. -/
def rotateRightRun (left : Tree κ ν) (binding : κ × ν) (parts : RedPair κ ν) :
    Measured (Tree κ ν) Cost :=
  bind (nodeRun .black left binding parts.first) fun left =>
    bind (nodeRun .black parts.middle parts.upper parts.last) fun right =>
      nodeRun .red left parts.lower right

/-- Execute the source's red bypass, LL, LR, RL, RR and fallback in that order.
The balance call is charged here, including the red bypass. -/
def balanceRun (color : RBTree.RBColor) (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) : Measured (Tree κ ν) Cost :=
  bind (color, tick .balanceCalls 1 + tick .patternAttempts 1 +
      tick .datatypeObservations 1) fun
    | .red => nodeRun .red left (key, value) right
    | .black =>
        bind (leftPairRun left) fun
          | some parts => rotateLeftRun parts (key, value) right
          | none =>
              bind (rightPairRun left) fun
                | some parts => rotateLeftRun parts (key, value) right
                | none =>
                    bind (leftPairRun right) fun
                      | some parts => rotateRightRun left (key, value) parts
                      | none =>
                          bind (rightPairRun right) fun
                            | some parts => rotateRightRun left (key, value) parts
                            | none => nodeRun .black left (key, value) right

/-- A red root does not inspect either child for a pattern. -/
theorem balanceRun_red (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    balanceRun .red left key value right =
      (.node .red left (key, value) right,
        tick .balanceCalls 1 + tick .patternAttempts 1 +
          tick .datatypeObservations 1 + tick .nodeConstructions 1) := rfl


@[simp] theorem redNodeRun_nil :
    redNodeRun (.nil : Tree κ ν) = (none, tick .datatypeObservations 1) := by
  apply Prod.ext
  · rfl
  · funext metric; cases metric <;> rfl

@[simp] theorem redNodeRun_black (left : Tree κ ν) (binding : κ × ν)
    (right : Tree κ ν) :
    redNodeRun (.node .black left binding right) =
      (none, tick .datatypeObservations 2) := by
  apply Prod.ext
  · rfl
  · funext metric; cases metric <;> rfl

@[simp] theorem redNodeRun_red (left : Tree κ ν) (binding : κ × ν)
    (right : Tree κ ν) :
    redNodeRun (.node .red left binding right) =
      (some ⟨left, binding, right⟩, tick .datatypeObservations 2) := by
  apply Prod.ext
  · rfl
  · funext metric; cases metric <;> rfl

theorem leftPairRun_value (t : Tree κ ν) :
    (leftPairRun t).1 = match t with
      | .node .red (.node .red a x b) y c => some ⟨a, x, b, y, c⟩
      | _ => none := by
  cases t with
  | nil => rfl
  | node color left binding right =>
      cases color with
      | black => rfl
      | red => cases left with
          | nil => rfl
          | node color a x b => cases color <;> rfl

theorem rightPairRun_value (t : Tree κ ν) :
    (rightPairRun t).1 = match t with
      | .node .red a x (.node .red b y c) => some ⟨a, x, b, y, c⟩
      | _ => none := by
  cases t with
  | nil => rfl
  | node color left binding right =>
      cases color with
      | black => rfl
      | red => cases right with
          | nil => rfl
          | node color b y c => cases color <;> rfl

/-- Only pattern attempts and performed node/color observations are charged. -/
theorem leftPairRun_cost (t : Tree κ ν) :
    (leftPairRun t).2 = tick .patternAttempts 1 +
      tick .datatypeObservations ((leftPairRun t).2 .datatypeObservations) := by
  cases t with
  | nil => funext metric; cases metric <;> rfl
  | node color left binding right =>
      cases color with
      | black => funext metric; cases metric <;> rfl
      | red => cases left with
          | nil => funext metric; cases metric <;> rfl
          | node color a x b => cases color <;> funext metric <;> cases metric <;> rfl

theorem rightPairRun_cost (t : Tree κ ν) :
    (rightPairRun t).2 = tick .patternAttempts 1 +
      tick .datatypeObservations ((rightPairRun t).2 .datatypeObservations) := by
  cases t with
  | nil => funext metric; cases metric <;> rfl
  | node color left binding right =>
      cases color with
      | black => funext metric; cases metric <;> rfl
      | red => cases right with
          | nil => funext metric; cases metric <;> rfl
          | node color a x b => cases color <;> funext metric <;> cases metric <;> rfl

theorem leftPairRun_observations_le (t : Tree κ ν) :
    (leftPairRun t).2 .datatypeObservations ≤ 4 := by
  cases t with
  | nil => exact (by decide : 1 ≤ 4)
  | node color left binding right =>
      cases color with
      | black => exact (by decide : 2 ≤ 4)
      | red => cases left with
          | nil => exact (by decide : 3 ≤ 4)
          | node color a x b => cases color <;> exact Nat.le_refl 4

theorem rightPairRun_observations_le (t : Tree κ ν) :
    (rightPairRun t).2 .datatypeObservations ≤ 4 := by
  cases t with
  | nil => exact (by decide : 1 ≤ 4)
  | node color left binding right =>
      cases color with
      | black => exact (by decide : 2 ≤ 4)
      | red => cases right with
          | nil => exact (by decide : 3 ≤ 4)
          | node color a x b => cases color <;> exact Nat.le_refl 4

@[simp] theorem leftPairRun_attempts (t : Tree κ ν) :
    (leftPairRun t).2 .patternAttempts = 1 := by
  rw [leftPairRun_cost]
  simp [tick]

@[simp] theorem rightPairRun_attempts (t : Tree κ ν) :
    (rightPairRun t).2 .patternAttempts = 1 := by
  rw [rightPairRun_cost]
  simp [tick]

theorem leftPairRun_other (t : Tree κ ν) (metric : Metric)
    (notPattern : metric ≠ .patternAttempts) (notDatatype : metric ≠ .datatypeObservations) :
    (leftPairRun t).2 metric = 0 := by
  rw [leftPairRun_cost]
  simp [tick, notPattern, notDatatype]

theorem rightPairRun_other (t : Tree κ ν) (metric : Metric)
    (notPattern : metric ≠ .patternAttempts) (notDatatype : metric ≠ .datatypeObservations) :
    (rightPairRun t).2 metric = 0 := by
  rw [rightPairRun_cost]
  simp [tick, notPattern, notDatatype]

theorem rotateLeftRun_exact (parts : RedPair κ ν) (binding : κ × ν)
    (right : Tree κ ν) :
    rotateLeftRun parts binding right =
      (.node .red (.node .black parts.first parts.lower parts.middle)
        parts.upper (.node .black parts.last binding right), tick .nodeConstructions 3) := by
  simp [rotateLeftRun, bind, nodeRun, ← tick_add]

theorem rotateRightRun_exact (left : Tree κ ν) (binding : κ × ν)
    (parts : RedPair κ ν) :
    rotateRightRun left binding parts =
      (.node .red (.node .black left binding parts.first)
        parts.lower (.node .black parts.middle parts.upper parts.last), tick .nodeConstructions 3) := by
  simp [rotateRightRun, bind, nodeRun, ← tick_add]


private theorem balanceRight_value (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) :
    (bind (leftPairRun right) fun
      | some parts => rotateRightRun left (key, value) parts
      | none => bind (rightPairRun right) fun
          | some parts => rotateRightRun left (key, value) parts
          | none => nodeRun .black left (key, value) right).1 =
    (match right with
      | .node .red (.node .red b y c) z d =>
          .node .red (.node .black left (key, value) b) y (.node .black c z d)
      | .node .red b y (.node .red c z d) =>
          .node .red (.node .black left (key, value) b) y (.node .black c z d)
      | _ => .node .black left (key, value) right) := by
  cases right with
  | nil => rfl
  | node color l binding r =>
      cases color with
      | black => rfl
      | red =>
          cases l with
          | nil =>
              cases r with
              | nil => rfl
              | node color a x b => cases color <;> rfl
          | node color a x b =>
              cases color with
              | red => rfl
              | black =>
                  cases r with
                  | nil => rfl
                  | node color c y d => cases color <;> rfl

theorem balanceRun_value (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).1 =
      Search.RedBlack.balance color left key value right := by
  cases color with
  | red => rfl
  | black =>
      cases left with
      | nil => exact balanceRight_value _ _ _ _
      | node color l binding r =>
          cases color with
          | black => exact balanceRight_value _ _ _ _
          | red =>
              cases l with
              | nil =>
                  cases r with
                  | nil => exact balanceRight_value _ _ _ _
                  | node color a x b => cases color with
                      | red => rfl
                      | black => exact balanceRight_value _ _ _ _
              | node color a x b =>
                  cases color with
                  | red => rfl
                  | black =>
                      cases r with
                      | nil => exact balanceRight_value _ _ _ _
                      | node color c y d => cases color with
                          | red => rfl
                          | black => exact balanceRight_value _ _ _ _



/-- The first successful left-left recognition supplies both the result and exact costs. -/
theorem balanceRun_leftLeft (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) (parts : RedPair κ ν)
    (selected : (leftPairRun left).1 = some parts) :
    balanceRun .black left key value right =
      ((rotateLeftRun parts (key, value) right).1,
        tick .balanceCalls 1 + tick .patternAttempts 2 +
          tick .datatypeObservations (1 + (leftPairRun left).2 .datatypeObservations) +
            tick .nodeConstructions 3) := by
  apply Prod.ext
  · simp only [balanceRun, bind, selected]
  · simp only [balanceRun, bind, selected, rotateLeftRun_exact]
    funext metric
    cases metric <;> simp [tick, leftPairRun_other]

/-- Left-right is selected only after the complete left-left attempt fails. -/
theorem balanceRun_leftRight (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) (parts : RedPair κ ν)
    (notLeftLeft : (leftPairRun left).1 = none)
    (selected : (rightPairRun left).1 = some parts) :
    balanceRun .black left key value right =
      ((rotateLeftRun parts (key, value) right).1,
        tick .balanceCalls 1 + tick .patternAttempts 3 +
          tick .datatypeObservations (1 + (leftPairRun left).2 .datatypeObservations +
            (rightPairRun left).2 .datatypeObservations) + tick .nodeConstructions 3) := by
  apply Prod.ext
  · simp only [balanceRun, bind, notLeftLeft, selected]
  · simp only [balanceRun, bind, notLeftLeft, selected, rotateLeftRun_exact]
    funext metric
    cases metric <;> simp [tick, leftPairRun_other, rightPairRun_other, Nat.add_assoc]

/-- Both left-side attempts fail before right-left can be selected. -/
theorem balanceRun_rightLeft (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) (parts : RedPair κ ν)
    (notLeftLeft : (leftPairRun left).1 = none)
    (notLeftRight : (rightPairRun left).1 = none)
    (selected : (leftPairRun right).1 = some parts) :
    balanceRun .black left key value right =
      ((rotateRightRun left (key, value) parts).1,
        tick .balanceCalls 1 + tick .patternAttempts 4 +
          tick .datatypeObservations (1 + (leftPairRun left).2 .datatypeObservations +
            (rightPairRun left).2 .datatypeObservations +
            (leftPairRun right).2 .datatypeObservations) + tick .nodeConstructions 3) := by
  apply Prod.ext
  · simp only [balanceRun, bind, notLeftLeft, notLeftRight, selected]
  · simp only [balanceRun, bind, notLeftLeft, notLeftRight, selected, rotateRightRun_exact]
    funext metric
    cases metric <;> simp [tick, leftPairRun_other, rightPairRun_other, Nat.add_assoc]

/-- Right-right retains all three earlier failures, including right-left. -/
theorem balanceRun_rightRight (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) (parts : RedPair κ ν)
    (notLeftLeft : (leftPairRun left).1 = none)
    (notLeftRight : (rightPairRun left).1 = none)
    (notRightLeft : (leftPairRun right).1 = none)
    (selected : (rightPairRun right).1 = some parts) :
    balanceRun .black left key value right =
      ((rotateRightRun left (key, value) parts).1,
        tick .balanceCalls 1 + tick .patternAttempts 5 +
          tick .datatypeObservations (1 + (leftPairRun left).2 .datatypeObservations +
            (rightPairRun left).2 .datatypeObservations +
            (leftPairRun right).2 .datatypeObservations +
            (rightPairRun right).2 .datatypeObservations) + tick .nodeConstructions 3) := by
  apply Prod.ext
  · simp only [balanceRun, bind, notLeftLeft, notLeftRight, notRightLeft, selected]
  · simp only [balanceRun, bind, notLeftLeft, notLeftRight, notRightLeft, selected,
      rotateRightRun_exact]
    funext metric
    cases metric <;> simp [tick, leftPairRun_other, rightPairRun_other, Nat.add_assoc]

/-- Black fallback observes all four failed complete patterns. -/
theorem balanceRun_fallback (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν)
    (notLeftLeft : (leftPairRun left).1 = none)
    (notLeftRight : (rightPairRun left).1 = none)
    (notRightLeft : (leftPairRun right).1 = none)
    (notRightRight : (rightPairRun right).1 = none) :
    balanceRun .black left key value right =
      (.node .black left (key, value) right,
        tick .balanceCalls 1 + tick .patternAttempts 5 +
          tick .datatypeObservations (1 + (leftPairRun left).2 .datatypeObservations +
            (rightPairRun left).2 .datatypeObservations +
            (leftPairRun right).2 .datatypeObservations +
            (rightPairRun right).2 .datatypeObservations) + tick .nodeConstructions 1) := by
  apply Prod.ext
  · simp only [balanceRun, bind, notLeftLeft, notLeftRight, notRightLeft, notRightRight,
      nodeRun_value]
  · simp only [balanceRun, bind, notLeftLeft, notLeftRight, notRightLeft, notRightRight,
      nodeRun_cost]
    funext metric
    cases metric <;> simp [tick, leftPairRun_other, rightPairRun_other, Nat.add_assoc]


/-- All balance costs have this sparse form. The bound on datatype observations
retains the actual number of fresh complete-pattern attempts. -/
theorem balanceRun_cost_form (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    ∃ p d a : Nat,
      (balanceRun color left key value right).2 =
        tick .balanceCalls 1 + tick .patternAttempts p +
          tick .datatypeObservations d + tick .nodeConstructions a ∧
      1 ≤ p ∧ p ≤ 5 ∧ d ≤ 1 + 4 * (p - 1) ∧ d ≤ 17 ∧ (a = 1 ∨ a = 3) := by
  have hl := leftPairRun_observations_le left
  have hl' := rightPairRun_observations_le left
  have hr := leftPairRun_observations_le right
  have hr' := rightPairRun_observations_le right
  cases color with
  | red => exact ⟨1, 1, 1, rfl, by decide, by decide, by decide, by decide, Or.inl rfl⟩
  | black =>
      cases hll : (leftPairRun left).1 with
      | some parts =>
          refine ⟨2, 1 + (leftPairRun left).2 .datatypeObservations, 3,
            congrArg Prod.snd (balanceRun_leftLeft left key value right parts hll),
            by decide, by decide, ?_, ?_, Or.inr rfl⟩ <;> omega
      | none =>
          cases hlr : (rightPairRun left).1 with
          | some parts =>
              refine ⟨3, 1 + (leftPairRun left).2 .datatypeObservations +
                (rightPairRun left).2 .datatypeObservations, 3,
                congrArg Prod.snd (balanceRun_leftRight left key value right parts hll hlr),
                by decide, by decide, ?_, ?_, Or.inr rfl⟩ <;> omega
          | none =>
              cases hrl : (leftPairRun right).1 with
              | some parts =>
                  refine ⟨4, 1 + (leftPairRun left).2 .datatypeObservations +
                    (rightPairRun left).2 .datatypeObservations +
                    (leftPairRun right).2 .datatypeObservations, 3,
                    congrArg Prod.snd (balanceRun_rightLeft left key value right parts hll hlr hrl),
                    by decide, by decide, ?_, ?_, Or.inr rfl⟩ <;> omega
              | none =>
                  cases hrr : (rightPairRun right).1 with
                  | some parts =>
                      refine ⟨5, 1 + (leftPairRun left).2 .datatypeObservations +
                        (rightPairRun left).2 .datatypeObservations +
                        (leftPairRun right).2 .datatypeObservations +
                        (rightPairRun right).2 .datatypeObservations, 3,
                        congrArg Prod.snd
                          (balanceRun_rightRight left key value right parts hll hlr hrl hrr),
                        by decide, by decide, ?_, ?_, Or.inr rfl⟩ <;> omega
                  | none =>
                      refine ⟨5, 1 + (leftPairRun left).2 .datatypeObservations +
                        (rightPairRun left).2 .datatypeObservations +
                        (leftPairRun right).2 .datatypeObservations +
                        (rightPairRun right).2 .datatypeObservations, 1,
                        congrArg Prod.snd (balanceRun_fallback left key value right hll hlr hrl hrr),
                        by decide, by decide, ?_, ?_, Or.inl rfl⟩ <;> omega

@[simp] theorem balanceRun_balanceCalls (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .balanceCalls = 1 := by
  obtain ⟨p, d, a, form, _⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simp [tick]

theorem balanceRun_patternAttempts_pos (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    1 ≤ (balanceRun color left key value right).2 .patternAttempts := by
  obtain ⟨p, d, a, form, positive, _⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simpa [tick] using positive

theorem balanceRun_patternAttempts_le (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .patternAttempts ≤ 5 := by
  obtain ⟨p, d, a, form, _, bound, _⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simpa [tick] using bound

theorem balanceRun_datatypeObservations_refined (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .datatypeObservations ≤
      1 + 4 * ((balanceRun color left key value right).2 .patternAttempts - 1) := by
  obtain ⟨p, d, a, form, _, _, bound, _⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simpa [tick] using bound

theorem balanceRun_datatypeObservations_le (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .datatypeObservations ≤ 17 := by
  obtain ⟨p, d, a, form, _, _, _, bound, _⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simpa [tick] using bound

theorem balanceRun_nodeConstructions_cases (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .nodeConstructions = 1 ∨
      (balanceRun color left key value right).2 .nodeConstructions = 3 := by
  obtain ⟨p, d, a, form, _, _, _, _, alternatives⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simpa [tick] using alternatives

theorem balanceRun_nodeConstructions_le (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .nodeConstructions ≤ 3 := by
  have alternatives := balanceRun_nodeConstructions_cases color left key value right
  omega

theorem balanceRun_other (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) (metric : Metric)
    (notBalance : metric ≠ .balanceCalls) (notPattern : metric ≠ .patternAttempts)
    (notDatatype : metric ≠ .datatypeObservations) (notNode : metric ≠ .nodeConstructions) :
    (balanceRun color left key value right).2 metric = 0 := by
  obtain ⟨p, d, a, form, _⟩ := balanceRun_cost_form color left key value right
  rw [form]
  simp [tick, notBalance, notPattern, notDatatype, notNode]


end Resources.RedBlack
