import Applications.Trees.TraversalWork
import Applications.Resources.TreeFold

/-! Shape-sensitive work of the existing actual measured tree fold.
The callback contract concerns summaries reached by arbitrary finite child
trees at fixed parameters. No independent cost evaluator is introduced.
Source and statement assessment: `docs/research/fdsa-tree-traversal-work.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeFold
universe u v
variable {α : Type u} {β : Type v}

/-- Collect natural work when the actual combining callback costs an affine
function of its left input tree's size. The fixed coefficients may be zero.
This numerical collection does not reorder a generic ordered observation. -/
theorem run_cost_leftSizeSum (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (d c : Nat)
    (hcost : ∀ (l : BinaryTree α) (a : α) (r : BinaryTree α),
      (combineRun (run entry empty combineRun l).1 a
        (run entry empty combineRun r).1).2 = d * l.numNodes + c)
    (t : BinaryTree α) :
    (run entry empty combineRun t).2 = entry * (2 * t.numNodes + 1) +
      d * Trees.leftSizeSum t + c * t.numNodes := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      rw [run_node_cost, hcost l a r, ihl, ihr, Trees.leftSizeSum_node]
      simp only [BinaryTree.numNodes]
      ring

end Resources.TreeFold
