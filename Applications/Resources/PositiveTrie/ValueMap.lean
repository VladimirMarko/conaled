import Applications.Resources.Measured
import Applications.Search.PositiveTrie.Normalized

/-!
# Actual optional payload mapping with ordered callback observations

The constructor-argument traversal is root, left, right, as in BinaryTree.map
and its applicative traverse. A callback's returned value is stored and its
observation is accumulated in that order with explicit grouping. The executor
requires only addition and zero; identifying its collected observation uses
only the zero laws, without associativity or commutativity. This declares a source sequencing
model, not a native evaluation-schedule assertion.

Outer coordinates are recursive entries (including nil), payload callback
invocations, and emitted BinaryTree.node events. Callback work is separate.
None skips the callback; every raw node is rebuilt without pruning. Key-aware
mapi has different prefix work and is not assigned this cost by value equality.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.ValueMap

open Search.PositiveTrie Numerals.PositiveArithmetic

universe u v w
variable {α : Type u} {β : Type v} {C : Type w}

abbrev Counts := Nat × (Nat × Nat)
abbrev Cost (C : Type w) := Counts × C

def payloadRun [Zero C] (callback : α → Measured β C) :
    Option α → Measured (Option β) (Cost C)
  | none => (none, ((0, (0, 0)), 0))
  | some value =>
      let result := callback value
      (some result.1, ((0, (1, 0)), result.2))

theorem payloadRun_value [Zero C] (callback : α → Measured β C) (value : Option α) :
    (payloadRun callback value).1 = value.map (fun x => (callback x).1) := by
  cases value <;> rfl

theorem payloadRun_counts [Zero C] (callback : α → Measured β C) (value : Option α) :
    (payloadRun callback value).2.1 = (0, (if value.isSome then 1 else 0, 0)) := by
  cases value <;> rfl

def run [Add C] [Zero C] (callback : α → Measured β C) :
    SparseMap α → Measured (SparseMap β) (Cost C)
  | .nil => (.nil, ((1, (0, 0)), 0))
  | .node value left right =>
      bind ((), ((1, (0, 0)), 0)) (fun _ =>
        bind (payloadRun callback value) (fun nextValue =>
          bind (run callback left) (fun nextLeft =>
            bind (run callback right) (fun nextRight =>
              (.node nextValue nextLeft nextRight, ((0, (0, 1)), 0))))))

theorem run_value [Add C] [Zero C] (callback : α → Measured β C) (tree : SparseMap α) :
    (run callback tree).1 = SparseMap.map (fun x => (callback x).1) tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [run, bind_value, payloadRun_value, SparseMap.map, BinaryTree.map, ihl, ihr]

theorem run_value_of [Add C] [Zero C] (callback : α → Measured β C) (label : α → β)
    (erases : ∀ value, (callback value).1 = label value) (tree : SparseMap α) :
    (run callback tree).1 = SparseMap.map label tree := by
  rw [run_value]
  have h : (fun value => (callback value).1) = label := funext erases
  rw [h]

theorem run_counts [Add C] [Zero C] (callback : α → Measured β C) (tree : SparseMap α) :
    (run callback tree).2.1 =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree, tree.numNodes)) := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [run, bind, Prod.fst_add, payloadRun_counts, ihl, ihr,
        Prod.mk_add_mk, BinaryTree.numNodes, SparseMap.cardinal_node]
      ext <;> dsimp only <;> omega

theorem run_calls [Add C] [Zero C] (callback : α → Measured β C) (tree : SparseMap α) :
    (run callback tree).2.1.1 = 2 * tree.numNodes + 1 :=
  congrArg Prod.fst (run_counts callback tree)

theorem run_callbacks [Add C] [Zero C] (callback : α → Measured β C) (tree : SparseMap α) :
    (run callback tree).2.1.2.1 = SparseMap.cardinal tree :=
  congrArg (fun counts => counts.2.1) (run_counts callback tree)

theorem run_nodes [Add C] [Zero C] (callback : α → Measured β C) (tree : SparseMap α) :
    (run callback tree).2.1.2.2 = tree.numNodes :=
  congrArg (fun counts => counts.2.2) (run_counts callback tree)

/-- Ordered mathematical collection of the actual callback observations. -/
def observations [Add C] [Zero C] (callback : α → Measured β C) : SparseMap α → C
  | .nil => 0
  | .node value left right =>
      (payloadRun callback value).2.2 + (observations callback left + observations callback right)

theorem run_observations [AddZeroClass C] (callback : α → Measured β C) (tree : SparseMap α) :
    (run callback tree).2.2 = observations callback tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [run, bind, Prod.snd_add, zero_add, add_zero, ihl, ihr, observations]

theorem run_normalized [Add C] [Zero C] (callback : α → Measured β C) {tree : SparseMap α}
    (normal : SparseMap.Normalized tree) : SparseMap.Normalized (run callback tree).1 := by
  rw [run_value]
  exact SparseMap.normalized_map (fun value => (callback value).1) normal

theorem observations_le (callback : α → Measured β Nat) (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → (callback value).2 ≤ bound) :
    observations callback tree ≤ SparseMap.cardinal tree * bound := by
  induction tree with
  | nil => simp [observations, SparseMap.cardinal]
  | node value left right ihl ihr =>
      have hl := ihl (fun key value present => bounded (.bit0 key) value present)
      have hr := ihr (fun key value present => bounded (.bit1 key) value present)
      cases value with
      | none =>
          simp only [observations, payloadRun, Nat.zero_add, SparseMap.cardinal, Nat.add_mul]
          omega
      | some value =>
          have hv := bounded .one value rfl
          simp only [observations, payloadRun, SparseMap.cardinal, Nat.add_mul, Nat.one_mul]
          omega

theorem run_callback_work_le (callback : α → Measured β Nat) (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → (callback value).2 ≤ bound) :
    (run callback tree).2.2 ≤ SparseMap.cardinal tree * bound := by
  rw [run_observations]
  exact observations_le callback tree bound bounded

theorem run_total_work_le (callback : α → Measured β Nat) (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → (callback value).2 ≤ bound) :
    (run callback tree).2.1.1 + (run callback tree).2.1.2.1 +
        (run callback tree).2.1.2.2 + (run callback tree).2.2 ≤
      3 * tree.numNodes + SparseMap.cardinal tree + 1 + SparseMap.cardinal tree * bound := by
  have h := run_callback_work_le callback tree bound bounded
  rw [run_calls, run_callbacks, run_nodes]
  omega

theorem run_total_work_le_of_bitLength (callback : α → Measured β Nat)
    {tree : SparseMap α} (normal : SparseMap.Normalized tree) (bits work : Nat)
    (boundedBits : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bits)
    (boundedWork : ∀ key value, SparseMap.find key tree = some value → (callback value).2 ≤ work) :
    (run callback tree).2.1.1 + (run callback tree).2.1.2.1 +
        (run callback tree).2.1.2.2 + (run callback tree).2.2 ≤
      3 * (SparseMap.cardinal tree * bits) + SparseMap.cardinal tree + 1 +
        SparseMap.cardinal tree * work := by
  have hn := SparseMap.numNodes_le_cardinal_mul normal bits boundedBits
  have hw := run_total_work_le callback tree work boundedWork
  omega

end Resources.PositiveTrie.ValueMap
