import Applications.Resources.PositiveTrie.Pruning
import Applications.Resources.PositiveTrie.Cardinality
import Applications.Resources.PositiveTrie.ValueMap
import Applications.Resources.PositiveTrie.Choice
import Examples.PositiveFiniteTrieWork
import Mathlib.Algebra.FreeMonoid.Basic

/-! Connected cases for actual finite-trie primitive executions.
Expected values and source-event vectors were fixed before implementation in
checkpoint053's fifteen-case ledger. General laws and exact computations are
both exercised; source events do not assert physical allocation or native time.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveFinitePrimitiveWork

open Search.PositiveTrie Numerals.PositiveArithmetic
open Resources.PositiveTrie.Pruning Examples.PositiveFiniteTrieWork
open Resources.PositiveTrie Examples.ColoringSelection

theorem prune_empty :
    pruneRun id false .nil .nil = (.nil, (1, 0)) ∧
      pruneRun Option.isSome (none : Option Nat) .nil .nil = (.nil, (1, 0)) := by decide

theorem prune_occupied :
    pruneRun id true .nil .nil = (.node true .nil .nil, (1, 1)) ∧
      pruneRun Option.isSome (some (.nil : KeySet)) .nil .nil = (presentEmpty, (1, 1)) := by
  decide

theorem prune_retains_padding :
    pruneRun id false (padding 1) .nil = (.node false (padding 1) .nil, (1, 1)) := by
  decide

theorem prune_present_empty_value_client :
    (pruneRun Option.isSome (some (.nil : KeySet)) .nil .nil).1 =
      SparseMap.prune (some (.nil : KeySet)) .nil .nil :=
  pruneRun_map_value (some (.nil : KeySet)) .nil .nil

theorem prune_padding_calls_client (height : Nat) :
    (pruneRun id false (padding height) .nil).2.1 = 1 :=
  pruneRun_calls id false (padding height) .nil

theorem erase_nil :
    setEraseRun 8 .nil = (.nil, (1, (0, 0))) ∧
      mapEraseRun 8 (.nil : SparseMap Nat) = (.nil, (1, (0, 0))) := by decide

theorem erase_present :
    setEraseRun 8 set8 = (.nil, (4, (4, 0))) ∧
      mapEraseRun 8 map8 = (.nil, (4, (4, 0))) := by decide

theorem erase_absent_root :
    setEraseRun 1 set8 = (set8, (1, (1, 1))) ∧
      mapEraseRun 1 map8 = (map8, (1, (1, 1))) := by decide

theorem erase_absent_deeper :
    setEraseRun 16 set8 = (set8, (5, (4, 4))) ∧
      mapEraseRun 16 map8 = (map8, (5, (4, 4))) := by decide

theorem map_erasure_client : (mapEraseRun 8 map8).1 = .nil := by
  rw [mapEraseRun_value]
  exact map8_erase.1

theorem set_erasure_client : (setEraseRun 8 set8).1 = .nil := by
  rw [setEraseRun_value]
  exact set8_erase.1

theorem map_erase_normalized_client : SparseMap.Normalized (mapEraseRun 8 map8).1 :=
  mapEraseRun_normalized 8 map8_normalized

theorem set_erase_normalized_client : KeySet.Normalized (setEraseRun 8 set8).1 :=
  setEraseRun_normalized 8 set8_normalized

theorem map_erase_path_client :
    (mapEraseRun 16 map8).2.1 = (Resources.PositiveTrie.Finite.findRun 16 map8).2.1 :=
  eraseRun_calls_eq_look Option.isSome none 16 map8

theorem set_erase_path_client :
    (setEraseRun 16 set8).2.1 = (Resources.PositiveTrie.Finite.memRun 16 set8).2.1 :=
  eraseRun_calls_eq_look id false 16 set8

theorem map_erase_work_client :
    (mapEraseRun 8 map8).2.1 + (mapEraseRun 8 map8).2.2.1 +
      (mapEraseRun 8 map8).2.2.2 ≤ 3 * bitLength (8 : PosNum) :=
  mapEraseRun_work_le 8 map8

theorem set_erase_work_client :
    (setEraseRun 8 set8).2.1 + (setEraseRun 8 set8).2.2.1 +
      (setEraseRun 8 set8).2.2.2 ≤ 3 * bitLength (8 : PosNum) :=
  setEraseRun_work_le 8 set8

theorem erase_height_client : (setEraseRun 16 set8).2.1 ≤ set8.height + 1 :=
  eraseRun_calls_le_height id false 16 set8

theorem erase_attempts_height_client : (setEraseRun 16 set8).2.2.1 ≤ set8.height :=
  eraseRun_prunes_le_height id false 16 set8

theorem erase_nodes_client : (setEraseRun 16 set8).2.2.2 ≤ (setEraseRun 16 set8).2.2.1 :=
  eraseRun_nodes_le_prunes id false 16 set8

theorem erase_padding_root : setEraseRun 1 (padding 3) = (padding 3, (1, (1, 1))) := by
  decide

theorem erase_padding_path : setEraseRun 8 (padding 3) = (.nil, (4, (3, 0))) := by
  decide

theorem erase_padding_lookup_client (key : PosNum) (height : Nat) :
    (setEraseRun key (padding height)).2.1 = (lookRun false key (padding height)).2.1 :=
  eraseRun_calls_eq_look id false key (padding height)

theorem equal_output_nonzero_work :
    (setEraseRun 1 set8).1 = set8 ∧ (setEraseRun 1 set8).2.2.2 = 1 := by decide

theorem difference_shortcuts :
    diffRun .nil (padding 3) = (.nil, (1, (0, 0))) ∧
      diffRun set8 .nil = (set8, (1, (0, 0))) ∧
      diffRun (padding 3) .nil = (padding 3, (1, (0, 0))) := by decide

theorem difference_shortcut_value_client : (diffRun set8 .nil).1 = set8 :=
  diffRun_value set8 .nil

theorem difference_shortcut_not_normalized : ¬ KeySet.Normalized (diffRun (padding 3) .nil).1 := by
  simpa only [padding, diffRun] using difference_right_not_normalized

theorem zero_constructions_large_output :
    (diffRun set8 .nil).2.2.2 = 0 ∧ (diffRun set8 .nil).1.numNodes = 4 := by decide

theorem difference_identical :
    pairedNodes set8 set8 = 4 ∧ diffRun set8 set8 = (.nil, (9, (4, 0))) := by decide

theorem difference_padded_right :
    pairedNodes leftSet (padding 3) = 2 ∧
      diffRun leftSet (padding 3) = (leftSet, (5, (2, 2))) := by decide

theorem difference_partial_overlap :
    pairedNodes set8 (padding 3) = 3 ∧
      diffRun set8 (padding 3) = (set8, (7, (3, 3))) := by decide

theorem difference_value_client : (diffRun leftSet (padding 3)).1 = leftSet := by
  rw [diffRun_value]
  exact difference_values.1

theorem difference_normalization_client : KeySet.Normalized (diffRun leftSet (padding 3)).1 :=
  diffRun_normalized leftSet_normalized (padding 3)

theorem difference_calls_client :
    (diffRun set8 (padding 3)).2.1 = 2 * pairedNodes set8 (padding 3) + 1 :=
  diffRun_calls set8 (padding 3)

theorem difference_prunes_client :
    (diffRun set8 (padding 3)).2.2.1 = pairedNodes set8 (padding 3) :=
  diffRun_prunes set8 (padding 3)

theorem difference_nodes_client :
    (diffRun set8 (padding 3)).2.2.2 ≤ pairedNodes set8 (padding 3) :=
  diffRun_nodes_le set8 (padding 3)

theorem difference_both_raw_bounds :
    pairedNodes set8 (padding 3) ≤ set8.numNodes ∧
      pairedNodes set8 (padding 3) ≤ (padding 3).numNodes :=
  ⟨pairedNodes_le_left set8 (padding 3), pairedNodes_le_right set8 (padding 3)⟩

theorem difference_normalized_bit_bound :
    (diffRun set8 (padding 3)).2.1 + (diffRun set8 (padding 3)).2.2.1 +
      (diffRun set8 (padding 3)).2.2.2 ≤ 4 * (KeySet.cardinal set8 * 4) + 1 :=
  diffRun_work_le_of_bitLength set8_normalized (padding 3) 4 set8_bit_bound

theorem cardinality_nil :
    Cardinality.setRun Cardinality.unitPrice .nil = (0, ((1, (0, 0)), 0)) ∧
      Cardinality.mapRun Cardinality.unitPrice (.nil : SparseMap Nat) =
        (0, ((1, (0, 0)), 0)) := by decide

theorem cardinality_occupied_leaf :
    Cardinality.setRun Cardinality.unitPrice (.node true .nil .nil) =
        (1, ((3, (1, 1)), 2)) ∧
      Cardinality.mapRun Cardinality.unitPrice presentEmpty = (1, ((3, (1, 1)), 2)) := by
  decide

theorem cardinality_absent_leaf :
    Cardinality.mapRun Cardinality.unitPrice absentLeaf = (0, ((3, (1, 0)), 1)) := by
  decide

theorem cardinality_singletons :
    Cardinality.setRun Cardinality.unitPrice set8 = (1, ((9, (4, 1)), 5)) ∧
      Cardinality.mapRun Cardinality.unitPrice map8 = (1, ((9, (4, 1)), 5)) := by decide

theorem cardinality_padding :
    Cardinality.setRun Cardinality.unitPrice (padding 3) = (0, ((7, (3, 0)), 3)) := by
  decide

theorem cardinality_map_value_client :
    (Cardinality.mapRun Cardinality.unitPrice map8).1 = SparseMap.cardinal map8 :=
  Cardinality.mapRun_value Cardinality.unitPrice map8

theorem cardinality_set_counts_client :
    (Cardinality.setRun Cardinality.unitPrice set8).2.1 =
      (2 * set8.numNodes + 1, (set8.numNodes, KeySet.cardinal set8)) :=
  Cardinality.setRun_counts Cardinality.unitPrice set8

theorem cardinality_graph :
    Cardinality.mapRun Cardinality.unitPrice sourceGraph = (5, ((13, (6, 5)), 11)) := by
  decide

theorem cardinality_palette :
    Cardinality.setRun Cardinality.unitPrice palette = (3, ((7, (3, 3)), 6)) := by decide

theorem cardinality_source_totals :
    (Cardinality.mapRun Cardinality.unitPrice sourceGraph).2.1.1 +
        (Cardinality.mapRun Cardinality.unitPrice sourceGraph).2.2 = 24 ∧
      (Cardinality.setRun Cardinality.unitPrice palette).2.1.1 +
        (Cardinality.setRun Cardinality.unitPrice palette).2.2 = 13 := by decide

theorem cardinality_graph_bound_client :
    (Cardinality.mapRun Cardinality.unitPrice sourceGraph).2.1.1 +
        (Cardinality.mapRun Cardinality.unitPrice sourceGraph).2.2 ≤
      3 * (SparseMap.cardinal sourceGraph * 3) + SparseMap.cardinal sourceGraph + 1 :=
  Cardinality.mapRun_unit_work_le sourceGraph_normalized 3 sourceGraph_bit_bound

theorem cardinality_palette_bound_client :
    (Cardinality.setRun Cardinality.unitPrice palette).2.1.1 +
        (Cardinality.setRun Cardinality.unitPrice palette).2.2 ≤
      3 * (KeySet.cardinal palette * 2) + KeySet.cardinal palette + 1 :=
  Cardinality.setRun_unit_work_le palette_normalized 2 palette_bit_bound

theorem cardinality_graph_calls_client :
    (Cardinality.mapRun Cardinality.unitPrice sourceGraph).2.1.1 ≤
      2 * (SparseMap.cardinal sourceGraph * 3) + 1 :=
  Cardinality.mapRun_calls_le_of_bitLength Cardinality.unitPrice
    sourceGraph_normalized 3 sourceGraph_bit_bound

theorem cardinality_palette_calls_client :
    (Cardinality.setRun Cardinality.unitPrice palette).2.1.1 ≤
      2 * (KeySet.cardinal palette * 2) + 1 :=
  Cardinality.setRun_calls_le_of_bitLength Cardinality.unitPrice
    palette_normalized 2 palette_bit_bound

def firstOperandPrice (left _ : Nat) : Nat := left + 1

def leftTrueChain : KeySet := KeySet.add 4 (KeySet.add 2 (KeySet.add 1 .nil))

theorem different_arithmetic_bills :
    Cardinality.setRun firstOperandPrice palette = (3, ((7, (3, 3)), 9)) ∧
      Cardinality.setRun firstOperandPrice leftTrueChain = (3, ((7, (3, 3)), 12)) := by
  decide

theorem same_addition_counts_different_price :
    (Cardinality.setRun firstOperandPrice palette).2.1 =
        (Cardinality.setRun firstOperandPrice leftTrueChain).2.1 ∧
      (Cardinality.setRun firstOperandPrice palette).2.2 ≠
        (Cardinality.setRun firstOperandPrice leftTrueChain).2.2 := by decide

theorem actual_operand_bill_client :
    (Cardinality.setRun firstOperandPrice palette).2.2 =
      Cardinality.arithmeticWork id firstOperandPrice palette :=
  Cardinality.run_price id firstOperandPrice palette

def raisePayload (value : Nat) : Resources.Measured Nat Nat := (value + 100, value + 1)

def retainAdjacency (value : KeySet) : Resources.Measured KeySet Nat := (value, 1)

theorem map_nil :
    ValueMap.run raisePayload .nil = (.nil, ((1, (0, 0)), 0)) := by decide

theorem map_absent_leaf :
    ValueMap.run retainAdjacency absentLeaf = (absentLeaf, ((3, (0, 1)), 0)) := by decide

theorem map_present_empty :
    ValueMap.run retainAdjacency presentEmpty = (presentEmpty, ((3, (1, 1)), 1)) := by
  decide

theorem map_source_graph_counts :
    (ValueMap.run retainAdjacency sourceGraph).2 = ((13, (5, 6)), 5) := by decide

theorem map_source_graph_callback_client :
    (ValueMap.run retainAdjacency sourceGraph).2.1.2.1 = SparseMap.cardinal sourceGraph :=
  ValueMap.run_callbacks retainAdjacency sourceGraph

theorem map_source_graph_node_client :
    (ValueMap.run retainAdjacency sourceGraph).2.1.2.2 = sourceGraph.numNodes :=
  ValueMap.run_nodes retainAdjacency sourceGraph

theorem map_changed_payloads :
    SparseMap.elements (ValueMap.run raisePayload twoValues).1 = [(2, 109), (1, 107)] ∧
      (ValueMap.run raisePayload twoValues).2 = ((5, (2, 2)), 18) := by decide

theorem map_actual_value_client :
    (ValueMap.run raisePayload twoValues).1 = SparseMap.map (fun value => value + 100) twoValues :=
  ValueMap.run_value_of raisePayload (fun value => value + 100) (fun _ => rfl) twoValues

theorem map_actual_observation_client :
    (ValueMap.run raisePayload twoValues).2.2 = ValueMap.observations raisePayload twoValues :=
  ValueMap.run_observations raisePayload twoValues

theorem raisePayload_bound (key : PosNum) (value : Nat)
    (present : SparseMap.find key twoValues = some value) : (raisePayload value).2 ≤ 10 := by
  by_cases h2 : key = 2
  · subst key
    change (some 9 : Option Nat) = some value at present
    have hv := Option.some.inj present
    rw [← hv]
    decide
  · by_cases h1 : key = 1
    · subst key
      change (some 7 : Option Nat) = some value at present
      have hv := Option.some.inj present
      rw [← hv]
      decide
    · simp [twoValues, SparseMap.find_add, h2, h1] at present

theorem twoValues_bit_bound (key : PosNum) (value : Nat)
    (present : SparseMap.find key twoValues = some value) : bitLength key ≤ 2 := by
  by_cases h2 : key = 2
  · subst key
    decide
  · by_cases h1 : key = 1
    · subst key
      decide
    · simp [twoValues, SparseMap.find_add, h2, h1] at present

theorem map_callback_bound_client :
    (ValueMap.run raisePayload twoValues).2.2 ≤ SparseMap.cardinal twoValues * 10 :=
  ValueMap.run_callback_work_le raisePayload twoValues 10 raisePayload_bound

theorem map_total_bound_client :
    (ValueMap.run raisePayload twoValues).2.1.1 +
        (ValueMap.run raisePayload twoValues).2.1.2.1 +
        (ValueMap.run raisePayload twoValues).2.1.2.2 +
        (ValueMap.run raisePayload twoValues).2.2 ≤
      3 * (SparseMap.cardinal twoValues * 2) + SparseMap.cardinal twoValues + 1 +
        SparseMap.cardinal twoValues * 10 :=
  ValueMap.run_total_work_le_of_bitLength raisePayload twoValues_normalized
    2 10 twoValues_bit_bound raisePayload_bound

def tracePayload (value : Nat) : Resources.Measured Nat (FreeAddMonoid Nat) :=
  (value + 100, FreeAddMonoid.of value)

theorem map_callback_order :
    FreeAddMonoid.toList (ValueMap.run tracePayload twoValues).2.2 = [7, 9] := rfl

theorem map_callback_order_distinguishes_fold :
    FreeAddMonoid.toList (ValueMap.run tracePayload twoValues).2.2 ≠ [9, 7] := by decide

theorem map_ordered_observation_client :
    (ValueMap.run tracePayload twoValues).2.2 = ValueMap.observations tracePayload twoValues :=
  ValueMap.run_observations tracePayload twoValues

def constantPayload (_ : Nat) : Resources.Measured Nat Nat := (0, 0)

theorem map_constant_normalized : SparseMap.Normalized (ValueMap.run constantPayload twoValues).1 :=
  ValueMap.run_normalized constantPayload twoValues_normalized

theorem map_constant_keys :
    SparseMap.elements (ValueMap.run constantPayload twoValues).1 = [(2, 0), (1, 0)] := by
  decide

theorem choice_priorities :
    Choice.run (.node true (padding 8) (padding 8)) = (some 1, (1, 0)) ∧
      Choice.run (.node false (.node true .nil .nil) (.node true .nil .nil)) =
        (some 2, (2, 1)) ∧
      Choice.run (.node false .nil (.node true .nil .nil)) = (some 3, (3, 1)) := by decide

theorem choice_priority_value_clients :
    (Choice.run (.node true (padding 8) (padding 8))).1 = some 1 ∧
      (Choice.run (.node false (.node true .nil .nil) (.node true .nil .nil))).1 = some 2 ∧
      (Choice.run (.node false .nil (.node true .nil .nil))).1 = some 3 :=
  ⟨Choice.run_value _, Choice.run_value _, Choice.run_value _⟩

theorem choice_priority_wrapper_clients :
    (Choice.run (.node true (padding 8) (padding 8))).2.2 + 1 = bitLength (1 : PosNum) ∧
      (Choice.run (.node false (.node true .nil .nil) (.node true .nil .nil))).2.2 + 1 =
        bitLength (2 : PosNum) ∧
      (Choice.run (.node false .nil (.node true .nil .nil))).2.2 + 1 = bitLength (3 : PosNum) :=
  ⟨Choice.run_wrappers (tree := .node true (padding 8) (padding 8)) rfl,
    Choice.run_wrappers (tree := .node false (.node true .nil .nil) (.node true .nil .nil)) rfl,
    Choice.run_wrappers (tree := .node false .nil (.node true .nil .nil)) rfl⟩

theorem choice_singletons :
    Choice.run set8 = (some 8, (4, 3)) ∧
      Choice.run (KeySet.add 7 .nil) = (some 7, (5, 2)) := by decide

theorem choice_value_client : (Choice.run set8).1 = KeySet.choose set8 := Choice.run_value set8

theorem choice_wrapper_client : (Choice.run set8).2.2 + 1 = bitLength (8 : PosNum) :=
  Choice.run_wrappers (by decide : KeySet.choose set8 = some 8)

theorem choice_normalized_bound_client : (Choice.run set8).2.1 + 1 ≤ 2 * 4 :=
  Choice.run_calls_add_one_le_of_bitLength set8_normalized (by decide) 4 set8_bit_bound

def rightKey : Nat → PosNum
  | 0 => .one
  | height + 1 => .bit1 (rightKey height)

def rightSingleton : Nat → KeySet
  | 0 => .node true .nil .nil
  | height + 1 => .node false .nil (rightSingleton height)

theorem rightSingleton_eq_add (height : Nat) :
    rightSingleton height = KeySet.add (rightKey height) .nil := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simpa only [rightSingleton, rightKey, KeySet.add, Search.PositiveTrie.ins] using
        congrArg (fun tree : KeySet => BinaryTree.node false .nil tree) ih

theorem rightSingleton_nonempty (height : Nat) : rightSingleton height ≠ .nil := by
  cases height <;> simp [rightSingleton]

theorem rightSingleton_normalized (height : Nat) : KeySet.Normalized (rightSingleton height) := by
  rw [rightSingleton_eq_add]
  exact KeySet.normalized_add (rightKey height) KeySet.normalized_nil

theorem rightSingleton_cardinal (height : Nat) : KeySet.cardinal (rightSingleton height) = 1 := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [rightSingleton, KeySet.cardinal, ih, Nat.zero_add]

theorem rightSingleton_height (height : Nat) : (rightSingleton height).height = height + 1 := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [rightSingleton, BinaryTree.height, ih, Nat.zero_max]

theorem rightKey_length (height : Nat) : bitLength (rightKey height) = height + 1 := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [rightKey, bitLength_bit1, ih]

theorem rightSingleton_choice (height : Nat) :
    Choice.run (rightSingleton height) = (some (rightKey height), (2 * height + 1, height)) := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [rightSingleton, Choice.run, Resources.bind, ih, rightKey,
        Prod.mk_add_mk, Nat.zero_add, Nat.add_zero]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · dsimp only
          omega
        · rfl

theorem normalized_choice_height_bound_attained (height : Nat) :
    (Choice.run (rightSingleton height)).2.1 + 1 = 2 * (rightSingleton height).height := by
  rw [rightSingleton_choice, rightSingleton_height]
  dsimp only
  omega

theorem rightSingleton_public_bound (height : Nat) :
    (Choice.run (rightSingleton height)).2.1 + 1 ≤ 2 * (rightSingleton height).height :=
  Choice.run_calls_add_one_le_height (rightSingleton_normalized height) (rightSingleton_nonempty height)

theorem padding_choice (height : Nat) : Choice.run (padding height) = (none, (2 * height + 1, 0)) := by
  have absent := (KeySet.choose_none_iff (padding height)).mpr (padding_mem height)
  simpa only [padding_nodes] using Choice.run_of_none absent

theorem padding3_choice : Choice.run (padding 3) = (none, (7, 0)) := padding_choice 3

def delayedChoice (height : Nat) : KeySet := .node false (padding height) (.node true .nil .nil)

theorem delayedChoice_run (height : Nat) :
    Choice.run (delayedChoice height) = (some 3, (2 * height + 3, 1)) := by
  simp only [delayedChoice, Choice.run, Resources.bind, padding_choice, Prod.mk_add_mk]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · dsimp only
      omega
    · rfl

theorem delayedChoice_normalized_iff (height : Nat) :
    KeySet.Normalized (delayedChoice height) ↔ height = 0 := by
  constructor
  · intro normal
    exact (padding_normalized_iff height).mp normal.1
  · intro zero
    subst height
    exact ⟨trivial, ⟨trivial, trivial, Or.inl rfl⟩, Or.inr (Or.inr (by intro h; cases h))⟩

theorem fixed_chosen_key_unbounded (bound : Nat) :
    ∃ tree : KeySet, (Choice.run tree).1 = some 3 ∧ bound < (Choice.run tree).2.1 := by
  refine ⟨delayedChoice bound, ?_, ?_⟩
  · rw [delayedChoice_run]
  · rw [delayedChoice_run]
    dsimp only
    omega

def fullFalse3 : KeySet :=
  .node false (.node false (padding 1) (padding 1)) (.node false (padding 1) (padding 1))

theorem fullFalse3_observations :
    fullFalse3.numNodes = 7 ∧ fullFalse3.height = 3 ∧ Choice.run fullFalse3 = (none, (15, 0)) := by
  decide

theorem raw_height_bound_fails : ¬ (Choice.run fullFalse3).2.1 ≤ 2 * fullFalse3.height + 1 := by
  decide

theorem fullFalse3_not_normalized : ¬ KeySet.Normalized fullFalse3 := by
  intro normal
  have empty := Choice.eq_nil_of_normalized_none normal (by decide)
  cases empty

theorem raw_choice_bound_client : (Choice.run fullFalse3).2.1 ≤ 2 * fullFalse3.numNodes + 1 :=
  Choice.run_calls_le fullFalse3

theorem empty_choice_zero_bound : (Choice.run .nil).2.1 ≤ 2 * 0 + 1 :=
  Choice.run_calls_le_of_bitLength KeySet.normalized_nil 0 (by intro key h; simp at h)

theorem empty_cardinality_zero_bound :
    (Cardinality.setRun Cardinality.unitPrice .nil).2.1.1 +
        (Cardinality.setRun Cardinality.unitPrice .nil).2.2 ≤
      3 * (KeySet.cardinal .nil * 0) + KeySet.cardinal .nil + 1 :=
  Cardinality.setRun_unit_work_le KeySet.normalized_nil 0 (by intro key h; simp at h)

theorem palette_choice : Choice.run palette = (some 1, (1, 0)) := by decide

theorem palette_choice_bound_client : (Choice.run palette).2.1 ≤ 2 * 2 + 1 :=
  Choice.run_calls_le_of_bitLength palette_normalized 2 palette_bit_bound

end Examples.PositiveFinitePrimitiveWork
