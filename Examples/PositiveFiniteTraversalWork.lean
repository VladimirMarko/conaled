import Applications.Resources.WorkloadBounds
import Applications.Resources.PositiveTrie.Traversal
import Applications.Resources.PositiveTrie.MapFold
import Applications.Resources.PositiveTrie.SetFold
import Applications.Resources.PositiveTrie.KeyMap
import Applications.Resources.PositiveTrie.Enumeration
import Examples.PositiveFinitePrimitiveWork

/-!
Connected cases for actual finite-trie traversals. Checkpoint054's sixteen
prewritten groups and T06b fix values, order and source-event counts before
implementation. These examples consume general laws and preserve their premises.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveFiniteTraversalWork

open Search.PositiveTrie Numerals.PositiveArithmetic
open Examples.PositiveFiniteTrieWork Examples.PositiveFinitePrimitiveWork
open Resources.PositiveTrie

abbrev Allowed (command : PosNum × Nat) : Prop := command = (2, 9) ∨ command = (1, 7)

def saturating (command : PosNum × Nat) (state : Nat) : Resources.Measured Nat Nat :=
  (min (state + command.2) 10, state + 1)

theorem saturating_actual_run :
    Resources.run saturating (SparseMap.elements twoValues) 0 = (10, 11) := by decide

theorem twoValues_allowed : ∀ command ∈ SparseMap.elements twoValues, Allowed command := by
  intro command member
  change command ∈ [(2, 9), (1, 7)] at member
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

theorem saturating_work_client :
    (Resources.run saturating (SparseMap.elements twoValues) 0).2 ≤ 22 := by
  apply Resources.run_work_le_on saturating Allowed (fun state => state ≤ 10) 11
    (fun _ _ _ _ => Nat.min_le_right _ _) (fun _ _ _ h => by dsimp [saturating]; omega)
    (SparseMap.elements twoValues) twoValues_allowed 0 (by decide)

def domainStep (command : PosNum × Nat) (state : Nat) : Resources.Measured Nat Nat :=
  if command = (2, 9) ∨ command = (1, 7) then saturating command state else (11, 100)

theorem domainStep_closed (command : PosNum × Nat) (state : Nat)
    (input : Allowed command) (_initial : state ≤ 10) : (domainStep command state).1 ≤ 10 := by
  change (if Allowed command then saturating command state else (11, 100)).1 ≤ 10
  rw [ite_eq_left input]
  exact Nat.min_le_right _ _

theorem domainStep_bounded (command : PosNum × Nat) (state : Nat)
    (input : Allowed command) (initial : state ≤ 10) : (domainStep command state).2 ≤ 11 := by
  change (if Allowed command then saturating command state else (11, 100)).2 ≤ 11
  rw [ite_eq_left input]
  dsimp [saturating]
  omega

theorem restricted_invariant_client :
    (Resources.run domainStep (SparseMap.elements twoValues) 0).1 ≤ 10 :=
  Resources.run_invariant_on domainStep Allowed (fun state => state ≤ 10)
    domainStep_closed (SparseMap.elements twoValues) twoValues_allowed 0 (by decide)

theorem restricted_work_client :
    (Resources.run domainStep (SparseMap.elements twoValues) 0).2 ≤ 22 :=
  Resources.run_work_le_on domainStep Allowed (fun state => state ≤ 10) 11
    domainStep_closed domainStep_bounded (SparseMap.elements twoValues) twoValues_allowed 0
    (by decide)

theorem restricted_actual_run :
    Resources.run domainStep (SparseMap.elements twoValues) 0 = (10, 11) := by decide

theorem off_domain_failure :
    ¬ Allowed (3, 0) ∧ (domainStep (3, 0) 0).1 = 11 ∧
      ¬ (domainStep (3, 0) 0).1 ≤ 10 ∧ (domainStep (3, 0) 0).2 = 100 ∧
      ¬ (domainStep (3, 0) 0).2 ≤ 11 := by decide

theorem off_invariant_failure :
    Allowed (2, 9) ∧ (domainStep (2, 9) 11).2 = 12 ∧
      ¬ (domainStep (2, 9) 11).2 ≤ 11 := by decide

theorem changed_prefix_not_allowed :
    ¬ (∀ command ∈ SparseMap.elementsFrom twoValues 5, Allowed command) := by
  intro allAllowed
  have bad := allAllowed (9, 9) (by decide)
  exact (by decide : ¬ Allowed (9, 9)) bad

theorem twoValues_mass :
    Resources.PositiveTrie.Traversal.prefixMass twoValues 1 = 3 ∧
      Resources.PositiveTrie.Traversal.prefixMass twoValues 5 = 7 ∧
      Resources.PositiveTrie.Traversal.copiedCells twoValues = 1 := by decide

theorem sourceGraph_mass :
    Resources.PositiveTrie.Traversal.prefixMass Examples.ColoringSelection.sourceGraph 1 = 14 ∧
      Resources.PositiveTrie.Traversal.copiedCells Examples.ColoringSelection.sourceGraph = 5 := by
  decide

def decimalMap (_key : PosNum) (value state : Nat) : Resources.Measured Nat Nat :=
  (10 * state + value, state + 1)

theorem map_fold_actual_state : MapFold.run decimalMap twoValues 0 = (97, ((5, (2, (6, 2))), 11)) := by
  decide

theorem map_fold_counts_client : (MapFold.run decimalMap twoValues 0).2.1 = (5, (2, (6, 2))) := by
  rw [MapFold.run_counts]
  decide

theorem map_fold_outer_client : MapFold.outerWork (MapFold.run decimalMap twoValues 0).2.1 = 15 := by
  rw [MapFold.run, MapFold.runFrom_outer_work]
  decide

theorem map_fold_combined :
    MapFold.outerWork (MapFold.run decimalMap twoValues 0).2.1 +
      (MapFold.run decimalMap twoValues 0).2.2 = 26 := by decide

theorem map_fold_wrong_orders :
    Resources.run (fun command state => decimalMap command.1 command.2 state)
        [(1, 7), (2, 9)] 0 = (79, 9) ∧
      (decimalMap 2 9 0).2 + (decimalMap 1 7 0).2 = 2 := by decide

def traceMap (key : PosNum) (value state : Nat) :
    Resources.Measured Nat (FreeAddMonoid (PosNum × Nat × Nat)) :=
  (10 * state + value, FreeAddMonoid.of (key, value, state))

theorem map_trace_bridge_client :
    ((MapFold.run traceMap twoValues 0).1, (MapFold.run traceMap twoValues 0).2.2) =
      (97, FreeAddMonoid.of (2, 9, 0) + FreeAddMonoid.of (1, 7, 9)) := by
  rw [MapFold.run_callback]
  rfl

theorem map_trace_order : FreeAddMonoid.toList (MapFold.run traceMap twoValues 0).2.2 =
    [(2, 9, 0), (1, 7, 9)] :=
  congrArg (fun result => FreeAddMonoid.toList result.2) map_trace_bridge_client

theorem map_fold_restricted_client :
    (MapFold.run (fun key value => domainStep (key, value)) twoValues 0).2.2 ≤ 22 :=
  MapFold.runFrom_callback_work_le (fun key value => domainStep (key, value)) Allowed
    (fun state => state ≤ 10) 11 (fun key value => domainStep_closed (key, value))
    (fun key value => domainStep_bounded (key, value)) twoValues .one twoValues_allowed 0 (by decide)

theorem map_fold_restricted_state_client :
    (MapFold.run (fun key value => domainStep (key, value)) twoValues 0).1 ≤ 10 :=
  MapFold.runFrom_invariant_on (fun key value => domainStep (key, value)) Allowed
    (fun state => state ≤ 10) (fun key value => domainStep_closed (key, value))
    twoValues .one twoValues_allowed 0 (by decide)

def decimalSet (key : PosNum) (state : Nat) : Resources.Measured Nat Nat :=
  (10 * state + (key : Nat), state + 1)

theorem set_fold_actual_state :
    SetFold.run decimalSet Examples.ColoringSelection.palette 0 =
      (213, ((7, (3, (6, (5, 2)))), 26)) := by decide

theorem set_fold_counts_client :
    (SetFold.run decimalSet Examples.ColoringSelection.palette 0).2.1 = (7, (3, (6, (5, 2)))) := by
  rw [SetFold.run_counts]
  decide

theorem set_fold_outer_client :
    SetFold.outerWork (SetFold.run decimalSet Examples.ColoringSelection.palette 0).2.1 = 23 := by
  rw [SetFold.run, SetFold.runFrom_outer_work]
  decide

theorem set_fold_combined :
    SetFold.outerWork (SetFold.run decimalSet Examples.ColoringSelection.palette 0).2.1 +
      (SetFold.run decimalSet Examples.ColoringSelection.palette 0).2.2 = 49 := by decide

def traceSet (key : PosNum) (state : Nat) :
    Resources.Measured Nat (FreeAddMonoid (PosNum × Nat)) :=
  (10 * state + (key : Nat), FreeAddMonoid.of (key, state))

theorem set_trace_bridge_client :
    ((SetFold.run traceSet Examples.ColoringSelection.palette 0).1,
      (SetFold.run traceSet Examples.ColoringSelection.palette 0).2.2) =
      (213, FreeAddMonoid.of (2, 0) + (FreeAddMonoid.of (1, 2) + FreeAddMonoid.of (3, 21))) := by
  rw [SetFold.run_callback]
  rfl

theorem set_trace_order :
    FreeAddMonoid.toList (SetFold.run traceSet Examples.ColoringSelection.palette 0).2.2 =
      [(2, 0), (1, 2), (3, 21)] :=
  congrArg (fun result => FreeAddMonoid.toList result.2) set_trace_bridge_client

def collectKey (key : PosNum) (keys : List PosNum) : Resources.Measured (List PosNum) Nat :=
  (keys ++ [key], 0)

theorem reversed_prefix_keys :
    (SetFold.runFrom collectKey leftSet [] 5).1 = [10, 6] ∧
      (SetFold.runFrom collectKey leftSet [] 6).1 = [9, 5] ∧
      Traversal.reversalMass leftSet 5 = 7 ∧ Traversal.reversalMass leftSet 6 = 7 := by decide

theorem reversed_prefix_value_client :
    (SetFold.runFrom collectKey leftSet [] 5).1 =
      KeySet.foldFrom (fun key keys => keys ++ [key]) leftSet [] 5 :=
  SetFold.runFrom_value collectKey leftSet [] 5

abbrev GeneratedSetAllowed (key : PosNum) : Prop := key = 10 ∨ key = 6
abbrev GeneratedSetInvariant (keys : List PosNum) : Prop := ∀ key ∈ keys, GeneratedSetAllowed key

theorem generatedSet_closed (key : PosNum) (state : List PosNum)
    (input : GeneratedSetAllowed key) (initial : GeneratedSetInvariant state) :
    GeneratedSetInvariant (collectKey key state).1 := by
  intro query member
  change query ∈ state ++ [key] at member
  rcases List.mem_append.mp member with old | fresh
  · exact initial query old
  · rw [List.mem_singleton.mp fresh]
    exact input

theorem generatedSet_inputs :
    ∀ key ∈ (KeySet.rawKeys leftSet).map (Numerals.PositivePaths.reverseAppend 5), GeneratedSetAllowed key := by
  intro key member
  change key ∈ [(10 : PosNum), 6] at member
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

theorem set_restricted_invariant_client : GeneratedSetInvariant (SetFold.runFrom collectKey leftSet [] 5).1 :=
  SetFold.runFrom_invariant_on collectKey GeneratedSetAllowed GeneratedSetInvariant
    generatedSet_closed leftSet 5 generatedSet_inputs []
    (fun _ member => by simp only [List.not_mem_nil] at member)

theorem set_restricted_work_client : (SetFold.runFrom collectKey leftSet [] 5).2.2 ≤ 0 :=
  SetFold.runFrom_callback_work_le collectKey GeneratedSetAllowed GeneratedSetInvariant 0
    generatedSet_closed (fun _ _ _ _ => Nat.le_refl 0) leftSet 5 generatedSet_inputs []
    (fun _ member => by simp only [List.not_mem_nil] at member)

def keyPayload (key : PosNum) (value : Nat) :
    Resources.Measured Nat (FreeAddMonoid (PosNum × Nat)) :=
  (100 * (key : Nat) + value, FreeAddMonoid.of (key, value))

theorem key_map_local_entries :
    SparseMap.elements (KeyMap.run keyPayload twoValues).1 = [(2, 209), (1, 107)] ∧
      SparseMap.elements (KeyMap.runFrom keyPayload 5 twoValues).1 = [(2, 909), (1, 507)] := by decide

theorem key_map_counts_client :
    (KeyMap.run keyPayload twoValues).2.1 = (5, (2, (6, (2, 2)))) ∧
      (KeyMap.runFrom keyPayload 5 twoValues).2.1 = (5, (2, (14, (10, 2)))) := by
  constructor
  · rw [KeyMap.run_counts]; decide
  · rw [KeyMap.runFrom_counts]; decide

theorem key_map_order_client :
    FreeAddMonoid.toList (KeyMap.run keyPayload twoValues).2.2 = [(1, 7), (2, 9)] := by
  rw [KeyMap.run, KeyMap.runFrom_observations]
  rfl

theorem key_map_prefix_order_client :
    FreeAddMonoid.toList (KeyMap.runFrom keyPayload 5 twoValues).2.2 = [(5, 7), (9, 9)] := by
  rw [KeyMap.runFrom_observations]
  rfl

theorem key_map_shape_client :
    SparseMap.occupancyTree (KeyMap.runFrom keyPayload 5 twoValues).1 = SparseMap.occupancyTree twoValues :=
  KeyMap.runFrom_occupancyTree keyPayload 5 twoValues

theorem key_map_noninjective_normalized :
    SparseMap.Normalized (KeyMap.runFrom (fun _ => constantPayload) 5 twoValues).1 :=
  KeyMap.runFrom_normalized (fun _ => constantPayload) 5 twoValues_normalized

theorem key_map_changes_payload_type :
    SparseMap.cardinal (KeyMap.runFrom (fun _ (_ : Nat) => ((), (0 : Nat))) 5 twoValues).1 = 2 :=
  KeyMap.runFrom_cardinal (fun _ (_ : Nat) => ((), (0 : Nat))) 5 twoValues

theorem key_ignore_value_client :
    (KeyMap.runFrom (fun _ => raisePayload) 5 twoValues).1 = (ValueMap.run raisePayload twoValues).1 :=
  KeyMap.runFrom_key_ignore_value raisePayload 5 twoValues

theorem key_ignore_callback_bound_client :
    (KeyMap.runFrom (fun _ => raisePayload) 5 twoValues).2.2 ≤ SparseMap.cardinal twoValues * 10 :=
  KeyMap.runFrom_callback_work_le (fun _ => raisePayload) 5 twoValues 10 raisePayload_bound

theorem key_ignore_work_separation :
    KeyMap.outerWork (KeyMap.runFrom (fun _ => raisePayload) 5 twoValues).2.1 = 33 ∧
      (ValueMap.run raisePayload twoValues).2.1 = (5, (2, 2)) ∧
      KeyMap.outerWork (KeyMap.runFrom (fun _ => raisePayload) 5 twoValues).2.1 -
        ((ValueMap.run raisePayload twoValues).2.1.1 +
          (ValueMap.run raisePayload twoValues).2.1.2.1 +
          (ValueMap.run raisePayload twoValues).2.1.2.2) = 24 := by decide

theorem nil_traversals (p : PosNum) (state : Nat) (tail : List PosNum) :
    MapFold.runFrom decimalMap .nil state p = (state, ((1, 0, 0, 0), 0)) ∧
      SetFold.runFrom decimalSet .nil state p = (state, ((1, 0, 0, 0, 0), 0)) ∧
      KeyMap.runFrom (fun _ => raisePayload) p .nil = (.nil, ((1, 0, 0, 0, 0), 0)) ∧
      Enumeration.Map.runFrom (.nil : SparseMap Nat) p = ([], (1, 0, 0, 0, 0, 0)) ∧
      Enumeration.Set.runFrom .nil p tail = (tail, (1, 0, 0, 0, 0)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem enumeration_optional_leaves :
    Enumeration.Map.run presentEmpty = ([(1, .nil)], (3, 2, 0, 1, 0, 1)) ∧
      Enumeration.Map.run absentLeaf = ([], (3, 2, 0, 1, 0, 0)) ∧
      Enumeration.Map.outerWork (Enumeration.Map.run presentEmpty).2 = 7 ∧
      Enumeration.Map.outerWork (Enumeration.Map.run absentLeaf).2 = 6 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem fold_present_empty_callback :
    MapFold.run (fun _ (_ : KeySet) (state : Nat) => (state + 1, (1 : Nat))) presentEmpty 0 =
      (1, ((3, 1, 2, 0), 1)) ∧
      MapFold.run (fun _ (_ : KeySet) (state : Nat) => (state + 1, (1 : Nat))) absentLeaf 0 =
        (0, ((3, 0, 2, 0), 0)) := by decide

theorem map_enumeration_forward_prefix :
    Enumeration.Map.runFrom twoValues 5 = ([(9, 9), (5, 7)], (5, 14, 10, 3, 1, 2)) ∧
      Enumeration.Map.outerWork (Enumeration.Map.runFrom twoValues 5).2 = 35 := by decide

theorem map_enumeration_prefix_client :
    (Enumeration.Map.runFrom twoValues 5).1 = SparseMap.elementsFrom twoValues 5 :=
  Enumeration.Map.runFrom_value twoValues 5

theorem map_enumeration_copies :
    (Enumeration.Map.run twoValues).2 = (5, 6, 2, 3, 1, 2) ∧
      Enumeration.Map.outerWork (Enumeration.Map.run twoValues).2 = 19 ∧
      (Enumeration.Map.run map8).2 = (9, 20, 12, 7, 3, 1) ∧
      Enumeration.Map.outerWork (Enumeration.Map.run map8).2 = 52 ∧
      (Enumeration.Map.run (SparseMap.add 7 42 .nil)).2 = (7, 12, 6, 3, 0, 1) ∧
      Enumeration.Map.outerWork (Enumeration.Map.run (SparseMap.add 7 42 .nil)).2 = 29 := by decide

theorem map_enumeration_counts_client :
    (Enumeration.Map.run map8).2 = (9, 20, 12, 7, 3, 1) := by
  rw [Enumeration.Map.run_counts]
  decide

theorem append_terminal_is_per_node :
    (Enumeration.Map.run twoValues).2.2.2.2.1 = 3 ∧
      Traversal.copiedCells twoValues + 1 = 2 := by decide

theorem set_enumeration_tail :
    Enumeration.Set.runFrom Examples.ColoringSelection.palette 1 [42, 43] =
      ([2, 1, 3, 42, 43], (7, 6, 5, 2, 3)) ∧
      Enumeration.Set.outerWork (Enumeration.Set.run Examples.ColoringSelection.palette).2 = 23 ∧
      (Enumeration.Set.run set8).2 = (9, 8, 4, 3, 1) ∧
      Enumeration.Set.outerWork (Enumeration.Set.run set8).2 = 25 := by decide

theorem set_enumeration_arbitrary_tail_client (tail : List PosNum) :
    (Enumeration.Set.runFrom Examples.ColoringSelection.palette 1 tail).1 = [2, 1, 3] ++ tail :=
  Enumeration.Set.runFrom_tail Examples.ColoringSelection.palette 1 tail

theorem set_enumeration_tail_length_client (tail : List PosNum) :
    (Enumeration.Set.runFrom Examples.ColoringSelection.palette 1 tail).1.length = 3 + tail.length :=
  Enumeration.Set.runFrom_length Examples.ColoringSelection.palette 1 tail

theorem set_enumeration_cost_independence_client (leftTail rightTail : List PosNum) :
    (Enumeration.Set.runFrom Examples.ColoringSelection.palette 1 leftTail).2 =
      (Enumeration.Set.runFrom Examples.ColoringSelection.palette 1 rightTail).2 :=
  Enumeration.Set.runFrom_cost_independent Examples.ColoringSelection.palette 1 leftTail rightTail

theorem set_enumeration_reversed_prefix :
    (Enumeration.Set.runFrom leftSet 5 []).1 = [10, 6] ∧
      (Enumeration.Set.runFrom leftSet 6 []).1 = [9, 5] := by decide

theorem source_enumeration :
    (Enumeration.Map.run Examples.ColoringSelection.sourceGraph).2 = (13, 28, 16, 11, 5, 5) ∧
      Enumeration.Map.outerWork (Enumeration.Map.run Examples.ColoringSelection.sourceGraph).2 = 78 ∧
      ((Enumeration.Map.run Examples.ColoringSelection.sourceGraph).1.map Prod.fst) = [4, 2, 6, 1, 5] := by decide

theorem source_enumeration_value_client :
    (Enumeration.Map.run Examples.ColoringSelection.sourceGraph).1 =
      SparseMap.elements Examples.ColoringSelection.sourceGraph :=
  Enumeration.Map.run_value Examples.ColoringSelection.sourceGraph

def insertDomain (key : PosNum) (_value : KeySet) (state : KeySet) :
    Resources.Measured KeySet (Nat × Nat) := Finite.setAddRun key state

theorem source_domain_value_client :
    (MapFold.run insertDomain Examples.ColoringSelection.sourceGraph .nil).1 =
      Graphs.Coloring.nodes Examples.ColoringSelection.sourceGraph := by
  rw [MapFold.run_value]
  simp only [insertDomain, Finite.setAddRun_value, Graphs.Coloring.nodes, SparseMap.domain]

theorem source_domain_callback_bill_client :
    (MapFold.run insertDomain Examples.ColoringSelection.sourceGraph .nil).2.2 = (12, 12) := by
  have h := Resources.run_observation
    (fun (entry : PosNum × KeySet) state => insertDomain entry.1 entry.2 state)
    (fun entry => (bitLength entry.1, bitLength entry.1))
    (fun entry state => Finite.setAddRun_cost entry.1 state)
    (SparseMap.elements Examples.ColoringSelection.sourceGraph) .nil
  rw [← MapFold.run_callback] at h
  calc
    _ = _ := h
    _ = (12, 12) := by decide

theorem source_domain_outer_client :
    MapFold.outerWork (MapFold.run insertDomain Examples.ColoringSelection.sourceGraph .nil).2.1 = 62 := by
  rw [MapFold.run, MapFold.runFrom_outer_work]
  decide

theorem source_domain_combined :
    MapFold.outerWork (MapFold.run insertDomain Examples.ColoringSelection.sourceGraph .nil).2.1 +
      (MapFold.run insertDomain Examples.ColoringSelection.sourceGraph .nil).2.2.1 +
      (MapFold.run insertDomain Examples.ColoringSelection.sourceGraph .nil).2.2.2 = 86 := by
  rw [source_domain_outer_client, source_domain_callback_bill_client]
  rfl

/-- Explicit optional adaptation of the accepted Boolean padding fixture. -/
def mapPadding (height : Nat) : SparseMap Nat := BinaryTree.map (fun _ => none) (padding height)

theorem mapPadding_succ (height : Nat) :
    mapPadding (height + 1) = .node none (mapPadding height) .nil := rfl

theorem mapPadding_occupancy (height : Nat) : SparseMap.occupancyTree (mapPadding height) = padding height := by
  induction height with
  | zero => rfl
  | succ height ih =>
      change BinaryTree.node false (SparseMap.occupancyTree (mapPadding height)) .nil =
        BinaryTree.node false (padding height) .nil
      rw [ih]

theorem mapPadding_cardinal (height : Nat) : SparseMap.cardinal (mapPadding height) = 0 := by
  rw [← SparseMap.cardinal_occupancyTree, mapPadding_occupancy, padding_cardinal]

theorem mapPadding_nodes (height : Nat) : (mapPadding height).numNodes = height := by
  rw [← SparseMap.numNodes_occupancyTree, mapPadding_occupancy, padding_nodes]

theorem mapPadding_mass (height : Nat) : SparseMap.keyMass (mapPadding height) = 0 := by
  rw [← SparseMap.keyMass_occupancyTree, mapPadding_occupancy, padding_mass]

theorem mapPadding_normalized_iff (height : Nat) : SparseMap.Normalized (mapPadding height) ↔ height = 0 := by
  rw [← SparseMap.normalized_occupancyTree_iff, mapPadding_occupancy, padding_normalized_iff]

theorem padding_pathMass (height : Nat) :
    2 * Traversal.pathMass (padding height) = height * (height + 1) := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [padding, Traversal.pathMass, BinaryTree.numNodes, padding_nodes, Nat.add_zero]
      ring_nf at ih ⊢
      omega

theorem mapPadding_prefixMass (height : Nat) :
    2 * Traversal.prefixMass (mapPadding height) .one = height * (height + 1) := by
  rw [mapPadding, Traversal.prefixMass_map, Traversal.prefixMass_one]
  exact padding_pathMass height

theorem mapPadding_copiedCells (height : Nat) : Traversal.copiedCells (mapPadding height) = 0 := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [mapPadding_succ, Traversal.copiedCells, ih, mapPadding_cardinal, Nat.add_zero]

theorem padding_map_work (height : Nat) :
    Enumeration.Map.outerWork (Enumeration.Map.run (mapPadding height)).2 = 2 * height ^ 2 + 3 * height + 1 := by
  have mass := mapPadding_prefixMass height
  rw [Enumeration.Map.run, Enumeration.Map.runFrom_outer_work, mapPadding_nodes,
    mapPadding_copiedCells, mapPadding_cardinal]
  ring_nf at mass ⊢
  omega

theorem padding_set_work (height : Nat) (r : PosNum) (tail : List PosNum) :
    Enumeration.Set.outerWork (Enumeration.Set.runFrom (padding height) r tail).2 = 4 * height + 1 := by
  rw [Enumeration.Set.runFrom_outer_work, padding_nodes, Traversal.reversalMass,
    padding_mass, padding_cardinal]
  simp

theorem padding_three_vectors :
    (Enumeration.Map.run (mapPadding 3)).2 = (7, 12, 6, 3, 0, 0) ∧
      Enumeration.Map.outerWork (Enumeration.Map.run (mapPadding 3)).2 = 28 ∧
      (Enumeration.Set.run (padding 3)).2 = (7, 6, 0, 0, 0) ∧
      Enumeration.Set.outerWork (Enumeration.Set.run (padding 3)).2 = 13 := by decide

theorem padding_refutes_cardinality_only (bound : Nat) :
    ∃ tree : SparseMap Nat, SparseMap.cardinal tree = 0 ∧
      ¬ SparseMap.Normalized tree ∧ bound < Enumeration.Map.outerWork (Enumeration.Map.run tree).2 := by
  refine ⟨mapPadding (bound + 1), mapPadding_cardinal _, ?_, ?_⟩
  · rw [mapPadding_normalized_iff]; omega
  · rw [padding_map_work]; omega

theorem longSingleton_succ (height : Nat) :
    longSingleton (height + 1) = .node none (longSingleton height) .nil := rfl

theorem longSingleton_mass (height : Nat) : SparseMap.keyMass (longSingleton height) = height + 1 := by
  induction height with
  | zero => rfl
  | succ height ih =>
      rw [longSingleton_succ, SparseMap.keyMass_node]
      change SparseMap.keyMass (longSingleton height) + 0 + SparseMap.cardinal (longSingleton (height + 1)) = _
      rw [ih, longSingleton_cardinal]

theorem longSingleton_prefixMass (height : Nat) :
    2 * Traversal.prefixMass (longSingleton height) .one = (height + 1) * (height + 2) := by
  simp only [Traversal.prefixMass_one]
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [longSingleton_succ, Traversal.pathMass, BinaryTree.numNodes,
        longSingleton_nodes, Nat.add_zero]
      ring_nf at ih ⊢
      omega

theorem longSingleton_copiedCells (height : Nat) : Traversal.copiedCells (longSingleton height) = height := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [longSingleton_succ, Traversal.copiedCells, ih, longSingleton_cardinal, Nat.add_zero]

theorem longSingleton_enumeration_work (height : Nat) :
    Enumeration.Map.outerWork (Enumeration.Map.run (longSingleton height)).2 =
      2 * (height + 1) ^ 2 + 5 * (height + 1) := by
  have mass := longSingleton_prefixMass height
  rw [Enumeration.Map.run, Enumeration.Map.runFrom_outer_work, longSingleton_nodes,
    longSingleton_copiedCells, longSingleton_cardinal]
  ring_nf at mass ⊢
  omega

theorem longSingleton_set_work (height : Nat) :
    Enumeration.Set.outerWork (Enumeration.Set.run (SparseMap.occupancyTree (longSingleton height))).2 =
      6 * (height + 1) + 1 := by
  rw [Enumeration.Set.run, Enumeration.Set.runFrom_outer_work, Traversal.reversalMass_one,
    SparseMap.numNodes_occupancyTree, SparseMap.keyMass_occupancyTree, longSingleton_nodes,
    longSingleton_mass]
  omega

theorem longSingleton_endpoint_family (height : Nat) :
    SparseMap.Normalized (longSingleton height) ∧ SparseMap.cardinal (longSingleton height) = 1 ∧
      (longSingleton height).numNodes = bitLength (Resources.PositiveTrie.longKey height) ∧
      SparseMap.keyMass (longSingleton height) = bitLength (Resources.PositiveTrie.longKey height) := by
  rw [Resources.PositiveTrie.longKey_bitLength]
  exact ⟨longSingleton_normalized height, longSingleton_cardinal height,
    longSingleton_nodes height, longSingleton_mass height⟩

def rightMap (height : Nat) : SparseMap Nat := SparseMap.add (rightKey height) 42 .nil

theorem rightMap_succ (height : Nat) : rightMap (height + 1) = .node none .nil (rightMap height) := rfl

theorem rightMap_normalized (height : Nat) : SparseMap.Normalized (rightMap height) :=
  SparseMap.normalized_add (rightKey height) 42 SparseMap.normalized_nil

theorem rightMap_occupancy (height : Nat) : SparseMap.occupancyTree (rightMap height) = rightSingleton height := by
  induction height with
  | zero => rfl
  | succ height ih =>
      change BinaryTree.node false .nil (SparseMap.occupancyTree (rightMap height)) =
        BinaryTree.node false .nil (rightSingleton height)
      rw [ih]

theorem rightMap_cardinal (height : Nat) : SparseMap.cardinal (rightMap height) = 1 := by
  rw [← SparseMap.cardinal_occupancyTree, rightMap_occupancy, rightSingleton_cardinal]

theorem rightMap_nodes (height : Nat) : (rightMap height).numNodes = height + 1 := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [rightMap_succ, BinaryTree.numNodes, ih, Nat.zero_add]

theorem rightMap_mass (height : Nat) : SparseMap.keyMass (rightMap height) = height + 1 := by
  induction height with
  | zero => rfl
  | succ height ih =>
      rw [rightMap_succ, SparseMap.keyMass_node]
      change 0 + SparseMap.keyMass (rightMap height) + SparseMap.cardinal (rightMap (height + 1)) = _
      rw [ih, rightMap_cardinal]
      omega

theorem rightMap_prefixMass (height : Nat) :
    2 * Traversal.prefixMass (rightMap height) .one = (height + 1) * (height + 2) := by
  simp only [Traversal.prefixMass_one]
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [rightMap_succ, Traversal.pathMass, BinaryTree.numNodes, rightMap_nodes, Nat.zero_add]
      ring_nf at ih ⊢
      omega

theorem rightMap_copiedCells (height : Nat) : Traversal.copiedCells (rightMap height) = 0 := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [rightMap_succ, Traversal.copiedCells, SparseMap.cardinal, ih, Nat.zero_add]

theorem rightMap_enumeration_work (height : Nat) :
    Enumeration.Map.outerWork (Enumeration.Map.run (rightMap height)).2 =
      2 * (height + 1) ^ 2 + 3 * (height + 1) + 2 := by
  have mass := rightMap_prefixMass height
  rw [Enumeration.Map.run, Enumeration.Map.runFrom_outer_work, rightMap_nodes,
    rightMap_copiedCells, rightMap_cardinal]
  ring_nf at mass ⊢
  omega

theorem rightSingleton_enumeration_work (height : Nat) :
    Enumeration.Set.outerWork (Enumeration.Set.run (rightSingleton height)).2 = 6 * (height + 1) + 1 := by
  rw [← rightMap_occupancy, Enumeration.Set.run, Enumeration.Set.runFrom_outer_work,
    Traversal.reversalMass_one, SparseMap.numNodes_occupancyTree, SparseMap.keyMass_occupancyTree,
    rightMap_nodes, rightMap_mass]
  omega

theorem normalized_singleton_enumeration_unbounded (bound : Nat) :
    ∃ tree : SparseMap Nat, SparseMap.Normalized tree ∧ SparseMap.cardinal tree = 1 ∧
      bound < Enumeration.Map.outerWork (Enumeration.Map.run tree).2 := by
  refine ⟨longSingleton bound, longSingleton_normalized bound, longSingleton_cardinal bound, ?_⟩
  rw [longSingleton_enumeration_work]
  omega

theorem leaf_generated_bound (key : PosNum) (value : KeySet)
    (present : SparseMap.find key presentEmpty = some value) :
    bitLength (Numerals.PositivePaths.append 8 key) ≤ 4 := by
  cases key with
  | one => decide
  | bit0 key => simp only [presentEmpty, SparseMap.find_bit0_node, SparseMap.find_nil, reduceCtorEq] at present
  | bit1 key => simp only [presentEmpty, SparseMap.find_bit1_node, SparseMap.find_nil, reduceCtorEq] at present

theorem leaf_prefix_bound_client : Traversal.prefixMass presentEmpty 8 ≤ 1 * 4 :=
  Traversal.map_prefixMass_le presentEmpty_normalized 8 4 leaf_generated_bound

theorem leaf_unused_children_exceed_bound :
    Resources.PositivePaths.appendRun 8 2 = (16, (4, 3)) ∧
      Resources.PositivePaths.appendRun 8 3 = (24, (4, 3)) ∧
      bitLength (16 : PosNum) = 5 ∧ bitLength (24 : PosNum) = 5 := by decide

theorem nil_prefix_zero_bound_client (p : PosNum) :
    Traversal.prefixMass (.nil : SparseMap Nat) p ≤ 0 * 0 :=
  Traversal.map_prefixMass_le SparseMap.normalized_nil p 0
    (fun _ _ present => by simp only [SparseMap.find_nil, reduceCtorEq] at present)

theorem nil_map_enumeration_bound_client : Enumeration.Map.outerWork (Enumeration.Map.run (.nil : SparseMap Nat)).2 ≤ 1 :=
  Enumeration.Map.run_outer_work_le SparseMap.normalized_nil 0
    (fun _ _ present => by simp only [SparseMap.find_nil, reduceCtorEq] at present)

theorem nil_set_enumeration_bound_client : Enumeration.Set.outerWork (Enumeration.Set.run .nil).2 ≤ 1 :=
  Enumeration.Set.run_outer_work_le KeySet.normalized_nil 0
    (fun _ present => by simp only [KeySet.mem_nil, Bool.false_eq_true] at present)

theorem normalized_map_fold_bound_client : MapFold.outerWork (MapFold.run decimalMap twoValues 0).2.1 ≤ 35 :=
  MapFold.run_outer_work_le decimalMap twoValues_normalized 2 twoValues_bit_bound 0

theorem normalized_set_fold_bound_client :
    SetFold.outerWork (SetFold.run decimalSet Examples.ColoringSelection.palette 0).2.1 ≤ 37 :=
  SetFold.run_outer_work_le decimalSet sourcePalette_normalized 2 sourcePalette_bit_bound 0

theorem normalized_key_map_bound_client : KeyMap.outerWork (KeyMap.run keyPayload twoValues).2.1 ≤ 39 :=
  KeyMap.run_outer_work_le keyPayload twoValues_normalized 2 twoValues_bit_bound

theorem normalized_map_enumeration_bound_client : Enumeration.Map.outerWork (Enumeration.Map.run twoValues).2 ≤ 47 :=
  Enumeration.Map.run_outer_work_le twoValues_normalized 2 twoValues_bit_bound

theorem normalized_set_enumeration_bound_client :
    Enumeration.Set.outerWork (Enumeration.Set.run Examples.ColoringSelection.palette).2 ≤ 37 :=
  Enumeration.Set.run_outer_work_le sourcePalette_normalized 2 sourcePalette_bit_bound

end Examples.PositiveFiniteTraversalWork
