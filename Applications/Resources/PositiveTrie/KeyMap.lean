import Applications.Resources.PositivePaths
import Applications.Resources.PositiveTrie.Traversal
import Applications.Resources.PositiveTrie.ValueMap

/-!
# Actual key-aware payload mapping

The callback sees the generated forward key, while the result retains the
original local storage positions. Source sequencing is root, left, right.
Actual callback results, prefixes and subtrees are consumed in construction.
Counts are entries, callbacks, prefix entries, prefix wrappers and emitted nodes;
callback observations remain separate and need not commute.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.KeyMap

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositivePaths Traversal

universe u v w
variable {α : Type u} {β : Type v} {C : Type w}

abbrev Counts := Nat × (Nat × (Nat × (Nat × Nat)))
abbrev Cost (C : Type w) := Counts × C

def prefixRun [Zero C] (p branch : PosNum) : Measured PosNum (Cost C) :=
  reweight (fun cost => ((0, (0, (cost.1, (cost.2, 0)))), 0))
    (Resources.PositivePaths.appendRun p branch)

theorem prefixRun_value [Zero C] (p branch : PosNum) :
    (prefixRun (C := C) p branch).1 = append p branch := Resources.PositivePaths.appendRun_value p branch

theorem prefixRun_counts [Zero C] (p branch : PosNum) :
    (prefixRun (C := C) p branch).2.1 = (0, (0, (bitLength p, (bitLength p - 1, 0)))) := by
  simp only [prefixRun, reweight, Resources.PositivePaths.appendRun_cost]

/-- Reuse the accepted optional callback execution, retaining its returned value. -/
def payloadRun [Zero C] (callback : PosNum → α → Measured β C) (p : PosNum) (value : Option α) :
    Measured (Option β) (Cost C) :=
  reweight (fun cost => ((cost.1.1, (cost.1.2.1, (0, (0, cost.1.2.2)))), cost.2))
    (ValueMap.payloadRun (callback p) value)

theorem payloadRun_value [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (value : Option α) :
    (payloadRun callback p value).1 = value.map (fun x => (callback p x).1) :=
  ValueMap.payloadRun_value (callback p) value

theorem payloadRun_counts [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (value : Option α) :
    (payloadRun callback p value).2.1 = (0, (if value.isSome then 1 else 0, (0, (0, 0)))) := by
  simp only [payloadRun, reweight, ValueMap.payloadRun_counts]

def runFrom [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) : SparseMap α → Measured (SparseMap β) (Cost C)
  | .nil => (.nil, ((1, (0, (0, (0, 0)))), 0))
  | .node value left right =>
      bind ((), ((1, (0, (0, (0, 0)))), 0)) (fun _ =>
        bind (payloadRun callback p value) (fun nextValue =>
          bind (prefixRun p (.bit0 .one)) (fun leftKey =>
            bind (runFrom callback leftKey left) (fun nextLeft =>
              bind (prefixRun p (.bit1 .one)) (fun rightKey =>
                bind (runFrom callback rightKey right) (fun nextRight =>
                  (.node nextValue nextLeft nextRight, ((0, (0, (0, (0, 1)))), 0))))))))

def run [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (tree : SparseMap α) : Measured (SparseMap β) (Cost C) := runFrom callback .one tree

theorem runFrom_value [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    (runFrom callback p tree).1 = SparseMap.mapiFrom (fun key value => (callback key value).1) p tree := by
  induction tree generalizing p with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [runFrom, bind_value, prefixRun_value, payloadRun_value, SparseMap.mapiFrom, ihl, ihr]

theorem run_value [Add C] [Zero C] (callback : PosNum → α → Measured β C) (tree : SparseMap α) :
    (run callback tree).1 = SparseMap.mapiFrom (fun key value => (callback key value).1) .one tree :=
  runFrom_value callback .one tree

theorem runFrom_counts_add [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    let counts := (runFrom callback p tree).2.1
    (counts.1, (counts.2.1, (counts.2.2.1,
      (counts.2.2.2.1 + 2 * tree.numNodes, counts.2.2.2.2)))) =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree,
        (2 * prefixMass tree p, (2 * prefixMass tree p, tree.numNodes)))) := by
  induction tree generalizing p with
  | nil => simp [runFrom, prefixMass_nil, BinaryTree.numNodes, SparseMap.cardinal]
  | node value left right ihl ihr =>
      have hl := ihl (append p (.bit0 .one))
      have hr := ihr (append p (.bit1 .one))
      simp only [Prod.mk.injEq] at hl hr
      have positive := bitLength_pos p
      simp only [runFrom, bind, Prod.fst_add, prefixRun_value, prefixRun_counts,
        payloadRun_counts, BinaryTree.numNodes, SparseMap.cardinal_node, prefixMass_node]
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem runFrom_counts [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    (runFrom callback p tree).2.1 =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree,
        (2 * prefixMass tree p, (2 * (prefixMass tree p - tree.numNodes), tree.numNodes)))) := by
  have h := runFrom_counts_add callback p tree
  have lower := numNodes_le_prefixMass tree p
  simp only [Prod.mk.injEq] at h
  ext <;> dsimp only <;> omega

theorem run_counts [Add C] [Zero C] (callback : PosNum → α → Measured β C) (tree : SparseMap α) :
    (run callback tree).2.1 =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree,
        (2 * prefixMass tree .one, (2 * (prefixMass tree .one - tree.numNodes), tree.numNodes)))) :=
  runFrom_counts callback .one tree

/-- Mathematical root/left/right collection, without a commutativity assumption. -/
def observations [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) : SparseMap α → C
  | .nil => 0
  | .node value left right =>
      (ValueMap.payloadRun (callback p) value).2.2 +
        (observations callback (append p (.bit0 .one)) left +
          observations callback (append p (.bit1 .one)) right)

theorem runFrom_observations [AddZeroClass C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    (runFrom callback p tree).2.2 = observations callback p tree := by
  induction tree generalizing p with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [runFrom, bind, payloadRun, prefixRun, reweight, Prod.snd_add,
        Resources.PositivePaths.appendRun_value, zero_add, add_zero, ihl, ihr, observations]

theorem mapiFrom_occupancyTree (label : PosNum → α → β) (p : PosNum) (tree : SparseMap α) :
    SparseMap.occupancyTree (SparseMap.mapiFrom label p tree) = SparseMap.occupancyTree tree := by
  induction tree generalizing p with
  | nil => rfl
  | node value left right ihl ihr =>
      change BinaryTree.node (value.map (label p)).isSome
        (SparseMap.occupancyTree (SparseMap.mapiFrom label (append p (.bit0 .one)) left))
        (SparseMap.occupancyTree (SparseMap.mapiFrom label (append p (.bit1 .one)) right)) =
        BinaryTree.node value.isSome (SparseMap.occupancyTree left) (SparseMap.occupancyTree right)
      rw [ihl, ihr]
      cases value <;> rfl

theorem runFrom_occupancyTree [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    SparseMap.occupancyTree (runFrom callback p tree).1 = SparseMap.occupancyTree tree := by
  rw [runFrom_value, mapiFrom_occupancyTree]

theorem runFrom_numNodes [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) : (runFrom callback p tree).1.numNodes = tree.numNodes := by
  have h := congrArg BinaryTree.numNodes (runFrom_occupancyTree callback p tree)
  simpa only [SparseMap.numNodes_occupancyTree] using h

theorem runFrom_cardinal [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) : SparseMap.cardinal (runFrom callback p tree).1 = SparseMap.cardinal tree := by
  have h := congrArg KeySet.cardinal (runFrom_occupancyTree callback p tree)
  simpa only [SparseMap.cardinal_occupancyTree] using h

theorem runFrom_normalized_iff [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    SparseMap.Normalized (runFrom callback p tree).1 ↔ SparseMap.Normalized tree := by
  rw [← SparseMap.normalized_occupancyTree_iff, runFrom_occupancyTree,
    SparseMap.normalized_occupancyTree_iff]

theorem runFrom_normalized [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) {tree : SparseMap α} (normal : SparseMap.Normalized tree) :
    SparseMap.Normalized (runFrom callback p tree).1 := (runFrom_normalized_iff callback p tree).mpr normal

theorem runFrom_key_ignore_value [Add C] [Zero C] (callback : α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    (runFrom (fun _ => callback) p tree).1 = (ValueMap.run callback tree).1 := by
  rw [runFrom_value, SparseMap.mapiFrom_key_ignore, ValueMap.run_value]

theorem observations_le (callback : PosNum → α → Measured β Nat) (p : PosNum)
    (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → (callback (append p key) value).2 ≤ bound) :
    observations callback p tree ≤ SparseMap.cardinal tree * bound := by
  induction tree generalizing p with
  | nil => simp [observations, SparseMap.cardinal]
  | node value left right ihl ihr =>
      have hl := ihl (append p (.bit0 .one)) (by
        intro key value present
        simpa only [append_bit0] using bounded (.bit0 key) value present)
      have hr := ihr (append p (.bit1 .one)) (by
        intro key value present
        simpa only [append_bit1] using bounded (.bit1 key) value present)
      cases value with
      | none =>
          simp only [observations, ValueMap.payloadRun, Nat.zero_add, SparseMap.cardinal, Nat.add_mul]
          omega
      | some value =>
          have hv := bounded .one value rfl
          rw [append_one_right] at hv
          simp only [observations, ValueMap.payloadRun, SparseMap.cardinal, Nat.add_mul, Nat.one_mul]
          omega

theorem runFrom_callback_work_le (callback : PosNum → α → Measured β Nat) (p : PosNum)
    (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → (callback (append p key) value).2 ≤ bound) :
    (runFrom callback p tree).2.2 ≤ SparseMap.cardinal tree * bound := by
  rw [runFrom_observations]
  exact observations_le callback p tree bound bounded

def outerWork (counts : Counts) : Nat :=
  counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2.1 + counts.2.2.2.2

theorem runFrom_outer_work [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    (p : PosNum) (tree : SparseMap α) :
    outerWork (runFrom callback p tree).2.1 = 4 * prefixMass tree p + SparseMap.cardinal tree + tree.numNodes + 1 := by
  have h := runFrom_counts_add callback p tree
  simp only [Prod.mk.injEq] at h
  dsimp only [outerWork]
  omega

theorem run_outer_work_le [Add C] [Zero C] (callback : PosNum → α → Measured β C)
    {tree : SparseMap α} (normal : SparseMap.Normalized tree) (bits : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bits) :
    outerWork (run callback tree).2.1 ≤
      4 * SparseMap.cardinal tree * bits ^ 2 + SparseMap.cardinal tree * bits + SparseMap.cardinal tree + 1 := by
  have hn := SparseMap.numNodes_le_cardinal_mul normal bits bounded
  have hm := map_prefixMass_one_le normal bits bounded
  rw [run, runFrom_outer_work]
  simp only [Nat.mul_assoc]
  omega

theorem run_total_work_le (callback : PosNum → α → Measured β Nat)
    {tree : SparseMap α} (normal : SparseMap.Normalized tree) (bits work : Nat)
    (boundedBits : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bits)
    (boundedWork : ∀ key value, SparseMap.find key tree = some value → (callback key value).2 ≤ work) :
    outerWork (run callback tree).2.1 + (run callback tree).2.2 ≤
      4 * SparseMap.cardinal tree * bits ^ 2 + SparseMap.cardinal tree * bits + SparseMap.cardinal tree + 1 +
        SparseMap.cardinal tree * work :=
  Nat.add_le_add (run_outer_work_le callback normal bits boundedBits)
    (runFrom_callback_work_le callback .one tree work boundedWork)

end Resources.PositiveTrie.KeyMap
