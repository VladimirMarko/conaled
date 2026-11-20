import Applications.Resources.TreeFold
import Applications.Search.PositiveTrie.Normalized

/-!
# Cardinality traversal and actual addition operands

The existing measured tree fold executes left, right and the arithmetic
combiner, posting one traversal entry per invocation (including nil). Outer
counts are entries, child-sum additions and occupied increments. The separate
Nat observation prices each addition at its actual operands. Unit pricing is
a declared source model; another tariff retains its own collected bill.
The independent occupancy observation below is proof data, not another pass
inserted into the executor or into graph termination checks.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.Cardinality

open Search.PositiveTrie Numerals.PositiveArithmetic

universe u
variable {α : Type u}

abbrev Counts := Nat × (Nat × Nat)
abbrev Cost := Counts × Nat

def occupiedCount (occupied : α → Bool) (tree : BinaryTree α) : Nat :=
  KeySet.cardinal (tree.map occupied)

theorem occupiedCount_nil (occupied : α → Bool) : occupiedCount occupied .nil = 0 := rfl

theorem occupiedCount_node (occupied : α → Bool) (value : α) (left right : BinaryTree α) :
    occupiedCount occupied (.node value left right) =
      occupiedCount occupied left + occupiedCount occupied right +
        (if occupied value then 1 else 0) := by
  exact KeySet.cardinal_node (occupied value) (left.map occupied) (right.map occupied)

theorem occupiedCount_isSome (tree : SparseMap α) :
    occupiedCount Option.isSome tree = SparseMap.cardinal tree :=
  SparseMap.cardinal_occupancyTree tree

theorem occupiedCount_id (tree : KeySet) : occupiedCount id tree = KeySet.cardinal tree := by
  unfold occupiedCount
  rw [BinaryTree.id_map]

def combineRun (occupied : α → Bool) (price : Nat → Nat → Nat)
    (left : Nat) (value : α) (right : Nat) : Measured Nat Cost :=
  bind (left + right, ((0, (1, 0)), price left right)) (fun sum =>
    if occupied value then (sum + 1, ((0, (0, 1)), price sum 1)) else pure sum)

theorem combineRun_value (occupied : α → Bool) (price : Nat → Nat → Nat)
    (left : Nat) (value : α) (right : Nat) :
    (combineRun occupied price left value right).1 =
      left + right + (if occupied value then 1 else 0) := by
  cases h : occupied value <;> simp [combineRun, bind, pure, h]

theorem combineRun_counts (occupied : α → Bool) (price : Nat → Nat → Nat)
    (left : Nat) (value : α) (right : Nat) :
    (combineRun occupied price left value right).2.1 =
      (0, (1, if occupied value then 1 else 0)) := by
  cases h : occupied value <;> simp [combineRun, bind, pure, h]

theorem combineRun_price (occupied : α → Bool) (price : Nat → Nat → Nat)
    (left : Nat) (value : α) (right : Nat) :
    (combineRun occupied price left value right).2.2 =
      price left right + (if occupied value then price (left + right) 1 else 0) := by
  cases h : occupied value <;> simp [combineRun, bind, pure, h]

def run (occupied : α → Bool) (price : Nat → Nat → Nat) (tree : BinaryTree α) :
    Measured Nat Cost := TreeFold.run ((1, (0, 0)), 0) 0 (combineRun occupied price) tree

theorem run_nil (occupied : α → Bool) (price : Nat → Nat → Nat) :
    run occupied price .nil = (0, ((1, (0, 0)), 0)) := rfl

theorem run_node (occupied : α → Bool) (price : Nat → Nat → Nat)
    (value : α) (left right : BinaryTree α) :
    run occupied price (.node value left right) =
      let body := bind (run occupied price left) (fun l =>
        bind (run occupied price right) (fun r => combineRun occupied price l value r))
      (body.1, body.2 + ((1, (0, 0)), 0)) := rfl

theorem run_value (occupied : α → Bool) (price : Nat → Nat → Nat) (tree : BinaryTree α) :
    (run occupied price tree).1 = occupiedCount occupied tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      rw [run_node]
      simp only [bind_value, combineRun_value, ihl, ihr, occupiedCount_node]

theorem run_counts (occupied : α → Bool) (price : Nat → Nat → Nat) (tree : BinaryTree α) :
    (run occupied price tree).2.1 =
      (2 * tree.numNodes + 1, (tree.numNodes, occupiedCount occupied tree)) := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      rw [run_node]
      simp only [bind, Prod.fst_add, combineRun_counts, ihl, ihr, BinaryTree.numNodes,
        occupiedCount_node, Prod.mk_add_mk]
      ext <;> dsimp only <;> omega

theorem run_calls (occupied : α → Bool) (price : Nat → Nat → Nat) (tree : BinaryTree α) :
    (run occupied price tree).2.1.1 = 2 * tree.numNodes + 1 :=
  congrArg Prod.fst (run_counts occupied price tree)

theorem run_child_additions (occupied : α → Bool) (price : Nat → Nat → Nat)
    (tree : BinaryTree α) : (run occupied price tree).2.1.2.1 = tree.numNodes :=
  congrArg (fun counts => counts.2.1) (run_counts occupied price tree)

theorem run_occupied_additions (occupied : α → Bool) (price : Nat → Nat → Nat)
    (tree : BinaryTree α) : (run occupied price tree).2.1.2.2 = occupiedCount occupied tree :=
  congrArg (fun counts => counts.2.2) (run_counts occupied price tree)

/-- Collection of prices at reached child sums, used only as a cost observation. -/
def arithmeticWork (occupied : α → Bool) (price : Nat → Nat → Nat) : BinaryTree α → Nat
  | .nil => 0
  | .node value left right =>
      arithmeticWork occupied price left + arithmeticWork occupied price right +
        price (occupiedCount occupied left) (occupiedCount occupied right) +
          (if occupied value then
            price (occupiedCount occupied left + occupiedCount occupied right) 1 else 0)

theorem run_price (occupied : α → Bool) (price : Nat → Nat → Nat) (tree : BinaryTree α) :
    (run occupied price tree).2.2 = arithmeticWork occupied price tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      rw [run_node]
      simp only [bind, Prod.snd_add, Nat.add_zero, combineRun_price, run_value,
        ihl, ihr, arithmeticWork]
      omega

def unitPrice (_ _ : Nat) : Nat := 1

theorem arithmeticWork_unit (occupied : α → Bool) (tree : BinaryTree α) :
    arithmeticWork occupied unitPrice tree = tree.numNodes + occupiedCount occupied tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [arithmeticWork, unitPrice, ihl, ihr, BinaryTree.numNodes, occupiedCount_node]
      omega

theorem run_unit_price (occupied : α → Bool) (tree : BinaryTree α) :
    (run occupied unitPrice tree).2.2 = tree.numNodes + occupiedCount occupied tree := by
  rw [run_price, arithmeticWork_unit]

theorem run_unit_work (occupied : α → Bool) (tree : BinaryTree α) :
    (run occupied unitPrice tree).2.1.1 + (run occupied unitPrice tree).2.2 =
      3 * tree.numNodes + occupiedCount occupied tree + 1 := by
  rw [run_calls, run_unit_price]
  omega

def mapRun (price : Nat → Nat → Nat) (tree : SparseMap α) : Measured Nat Cost :=
  run Option.isSome price tree

def setRun (price : Nat → Nat → Nat) (tree : KeySet) : Measured Nat Cost :=
  run id price tree

theorem mapRun_value (price : Nat → Nat → Nat) (tree : SparseMap α) :
    (mapRun price tree).1 = SparseMap.cardinal tree := by
  rw [mapRun, run_value, occupiedCount_isSome]

theorem setRun_value (price : Nat → Nat → Nat) (tree : KeySet) :
    (setRun price tree).1 = KeySet.cardinal tree := by
  rw [setRun, run_value, occupiedCount_id]

theorem mapRun_counts (price : Nat → Nat → Nat) (tree : SparseMap α) :
    (mapRun price tree).2.1 =
      (2 * tree.numNodes + 1, (tree.numNodes, SparseMap.cardinal tree)) := by
  rw [mapRun, run_counts, occupiedCount_isSome]

theorem setRun_counts (price : Nat → Nat → Nat) (tree : KeySet) :
    (setRun price tree).2.1 =
      (2 * tree.numNodes + 1, (tree.numNodes, KeySet.cardinal tree)) := by
  rw [setRun, run_counts, occupiedCount_id]

theorem mapRun_unit_work (tree : SparseMap α) :
    (mapRun unitPrice tree).2.1.1 + (mapRun unitPrice tree).2.2 =
      3 * tree.numNodes + SparseMap.cardinal tree + 1 := by
  rw [mapRun, run_unit_work, occupiedCount_isSome]

theorem setRun_unit_work (tree : KeySet) :
    (setRun unitPrice tree).2.1.1 + (setRun unitPrice tree).2.2 =
      3 * tree.numNodes + KeySet.cardinal tree + 1 := by
  rw [setRun, run_unit_work, occupiedCount_id]

theorem mapRun_calls_le_of_bitLength (price : Nat → Nat → Nat) {tree : SparseMap α}
    (normal : SparseMap.Normalized tree) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bound) :
    (mapRun price tree).2.1.1 ≤ 2 * (SparseMap.cardinal tree * bound) + 1 := by
  have h := SparseMap.numNodes_le_cardinal_mul normal bound bounded
  rw [mapRun, run_calls]
  omega

theorem setRun_calls_le_of_bitLength (price : Nat → Nat → Nat) {tree : KeySet}
    (normal : KeySet.Normalized tree) (bound : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bound) :
    (setRun price tree).2.1.1 ≤ 2 * (KeySet.cardinal tree * bound) + 1 := by
  have h := KeySet.numNodes_le_cardinal_mul normal bound bounded
  rw [setRun, run_calls]
  omega

theorem mapRun_unit_work_le {tree : SparseMap α} (normal : SparseMap.Normalized tree)
    (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bound) :
    (mapRun unitPrice tree).2.1.1 + (mapRun unitPrice tree).2.2 ≤
      3 * (SparseMap.cardinal tree * bound) + SparseMap.cardinal tree + 1 := by
  have h := SparseMap.numNodes_le_cardinal_mul normal bound bounded
  rw [mapRun_unit_work]
  omega

theorem setRun_unit_work_le {tree : KeySet} (normal : KeySet.Normalized tree) (bound : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bound) :
    (setRun unitPrice tree).2.1.1 + (setRun unitPrice tree).2.2 ≤
      3 * (KeySet.cardinal tree * bound) + KeySet.cardinal tree + 1 := by
  have h := KeySet.numNodes_le_cardinal_mul normal bound bounded
  rw [setRun_unit_work]
  omega

end Resources.PositiveTrie.Cardinality
