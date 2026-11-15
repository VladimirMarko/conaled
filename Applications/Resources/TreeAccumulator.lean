import Applications.Trees.Observations
import Applications.Resources.CallCount
import Mathlib.Tactic.Ring

/-! Actual append-free suffix invocation, represented by an ordinary
function-valued tree fold. The observation belongs to invocation; separately
measuring construction requires a separate program. Source and statement
assessment: `docs/research/fdsa-tree-accumulator-invocation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeAccumulator
universe u v w
variable {α : Type u} {C : Type v} {D : Type w}

/-- Invoke the right child first, then the left on its actual returned suffix
with the root label consed. Post the entry observation after that body. -/
def nodeRun [Add C] (entry : C) (left : List α → Measured (List α) C)
    (a : α) (right : List α → Measured (List α) C) (suffix : List α) :
    Measured (List α) C :=
  let body := Resources.bind (right suffix) (fun rest => left (a :: rest))
  (body.1, body.2 + entry)

theorem nodeRun_eq [Add C] (entry : C) (left : List α → Measured (List α) C)
    (a : α) (right : List α → Measured (List α) C) (suffix : List α) :
    nodeRun entry left a right suffix =
      ((left (a :: (right suffix).1)).1,
        ((right suffix).2 + (left (a :: (right suffix).1)).2) + entry) := rfl

theorem nodeRun_value [Add C] (entry : C) (left : List α → Measured (List α) C)
    (a : α) (right : List α → Measured (List α) C) (suffix : List α) :
    (nodeRun entry left a right suffix).1 = (left (a :: (right suffix).1)).1 := rfl

theorem nodeRun_cost [Add C] (entry : C) (left : List α → Measured (List α) C)
    (a : α) (right : List α → Measured (List α) C) (suffix : List α) :
    (nodeRun entry left a right suffix).2 =
      ((right suffix).2 + (left (a :: (right suffix).1)).2) + entry := rfl

/-- The existing ordinary fold is the only tree recursion. Its summary is an
ordinary measured function; applying it executes the suffix recurrence. -/
def invoke [Add C] (entry : C) (t : BinaryTree α) : List α → Measured (List α) C :=
  Trees.fold (fun suffix => (suffix, entry)) (nodeRun entry) t

@[simp] theorem invoke_nil [Add C] (entry : C) (suffix : List α) :
    invoke entry .nil suffix = (suffix, entry) := rfl

theorem invoke_node [Add C] (entry : C) (a : α) (l r : BinaryTree α)
    (suffix : List α) :
    invoke entry (.node a l r) suffix =
      nodeRun entry (invoke entry l) a (invoke entry r) suffix := rfl

/-- This exact source-entry specialization retains both empty-child calls. -/
theorem invoke_node_tick (a : α) (l r : BinaryTree α) (suffix : List α) :
    invoke 1 (.node a l r) suffix =
      CallCount.tick (Resources.bind (invoke 1 r suffix) (fun rest => invoke 1 l (a :: rest))) := rfl

/-- The left induction hypothesis is used at the actual right result, for every
suffix. Append occurs in the specification, not the operation. -/
theorem invoke_value [Add C] (entry : C) (t : BinaryTree α) (suffix : List α) :
    (invoke entry t suffix).1 = Trees.inorder t ++ suffix := by
  induction t generalizing suffix with
  | nil => simp only [invoke_nil, Trees.inorder_nil, List.nil_append]
  | node a l r ihl ihr =>
      rw [invoke_node, nodeRun_value, ihr, ihl, Trees.inorder_node]
      simp only [List.append_assoc, List.cons_append]

/-- Transport preserves the same dependent child arguments and observation order. -/
theorem reweight_nodeRun [AddMonoid C] [AddMonoid D] (h : C →+ D) (entry : C)
    (left : List α → Measured (List α) C) (a : α)
    (right : List α → Measured (List α) C) (suffix : List α) :
    reweight h (nodeRun entry left a right suffix) =
      nodeRun (h entry) (fun s => reweight h (left s)) a
        (fun s => reweight h (right s)) suffix := by
  have hb := reweight_bind h (right suffix) (fun rest => left (a :: rest))
  simpa only [nodeRun, reweight, map_add] using
    congrArg (fun body : Measured (List α) D => (body.1, body.2 + h entry)) hb

theorem reweight_invoke [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (entry : C) (t : BinaryTree α) (suffix : List α) :
    reweight h (invoke entry t suffix) = invoke (h entry) t suffix := by
  have hf : (fun s => reweight h (invoke entry t s)) = invoke (h entry) t := by
    unfold invoke
    refine Trees.fold_fusion _ _ _ _
      (fun f : List α → Measured (List α) C => fun s => reweight h (f s)) rfl ?_ t
    intro left a right
    funext s
    exact reweight_nodeRun h entry left a right s
  exact congrFun hf suffix

/-- Uniformity over all suffixes justifies the cost of the actual left argument. -/
theorem invoke_cost (entry : Nat) (t : BinaryTree α) (suffix : List α) :
    (invoke entry t suffix).2 = entry * (2 * t.numNodes + 1) := by
  induction t generalizing suffix with
  | nil => simp
  | node a l r ihl ihr =>
      rw [invoke_node, nodeRun_cost, ihr, ihl]
      simp only [BinaryTree.numNodes]
      ring

theorem invoke_exact (entry : Nat) (t : BinaryTree α) (suffix : List α) :
    invoke entry t suffix = (Trees.inorder t ++ suffix, entry * (2 * t.numNodes + 1)) := by
  apply Prod.ext
  · exact invoke_value entry t suffix
  · exact invoke_cost entry t suffix

theorem invoke_length [Add C] (entry : C) (t : BinaryTree α) (suffix : List α) :
    (invoke entry t suffix).1.length = t.numNodes + suffix.length := by
  rw [invoke_value, List.length_append, Trees.inorder_length]

/-- Nil keeps its separate entry charge; the proportional bound needs `0 < n`. -/
theorem invoke_cost_linear (entry : Nat) (t : BinaryTree α) (suffix : List α)
    (hn : 0 < t.numNodes) : (invoke entry t suffix).2 ≤ 3 * entry * t.numNodes := by
  rw [invoke_cost]
  calc
    entry * (2 * t.numNodes + 1) ≤ entry * (2 * t.numNodes + t.numNodes) :=
      Nat.mul_le_mul_left entry (Nat.add_le_add_left (Nat.succ_le_of_lt hn) _)
    _ = 3 * entry * t.numNodes := by ring

end Resources.TreeAccumulator
