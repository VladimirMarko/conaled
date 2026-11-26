import Applications.Resources.PositiveTrie
import Examples.PositiveTries

/-!
# Measured positive trie paths and collision work

The worked costs count source calls and BinaryTree node constructions. Empty
lookup stops early, while insertion and lookup of its written key traverse the
whole positive representation. The all-left singleton family separates key
length from the number of distinct explicitly written keys.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveTrieWork

open Resources Resources.PositiveTrie

universe u

theorem ten_empty_lookup : lookRun false 10 .nil = (false, (1, 0)) := lookRun_nil false 10

theorem ten_empty_insert : (insertRun 10 true (Search.PositiveTrie.empty false)).2 = (4, 4) :=
  insertRun_cost 10 true _

theorem ten_insert_then_read :
    (bind (insertRun 10 true (Search.PositiveTrie.empty false)) (lookupRun 10)) =
      (true, (8, 4)) :=
  Prod.ext (insert_lookup_value 10 true _) (insert_lookup_cost 10 true _)

def sourceBuild : Measured (Search.PositiveTrie.Table Bool) Cost :=
  bind (insertRun 10 true (Search.PositiveTrie.empty false)) (insertRun 3 true)

theorem sourceBuild_value : sourceBuild.1 = PositiveTries.threeTenTable := by
  simp only [sourceBuild, bind_value, insertRun_value]
  rfl

theorem sourceBuild_cost : sourceBuild.2 = (6, 6) := by
  simp only [sourceBuild, Resources.bind, insertRun_cost]
  rfl

theorem source_measured_queries :
    [3, 1, 4, 1, 5].map (fun key : PosNum => lookupRun key PositiveTries.threeTenTable) =
      [(true, (2, 0)), (false, (1, 0)), (false, (3, 0)), (false, (1, 0)), (false, (3, 0))] := rfl

theorem overwrite_constructions_are_not_size_increase :
    (insertRun 10 false PositiveTries.threeTenTable).2 = (4, 4) ∧
      (insertRun 10 false PositiveTries.threeTenTable).1.2.numNodes =
        PositiveTries.threeTenTable.2.numNodes :=
  ⟨insertRun_cost 10 false _, rfl⟩

theorem different_raw_default :
    (insertRun 2 9 ((77 : Nat), .nil)).1.1 = 77 ∧
      lookupRun 1 (insertRun 2 9 ((77 : Nat), .nil)).1 = (77, (1, 0)) :=
  ⟨insertRun_default 2 9 _, rfl⟩

theorem higher_universe_costs (default value : Type u) :
    (insertRun 10 value (Search.PositiveTrie.empty default)).2 = (4, 4) ∧
      (lookupRun 10 (insertRun 10 value (Search.PositiveTrie.empty default)).1).1 = value :=
  ⟨insertRun_cost 10 value _, lookupRun_insertRun_value 10 value _⟩

theorem long_empty_early_stop (h : Nat) :
    lookRun "missing" (longKey h) .nil = ("missing", (1, 0)) := lookRun_nil _ _

theorem singleton_long_path (h : Nat) :
    Numerals.PositiveKeys.numeric (longKey h) = 2 ^ h ∧
      Numerals.PositiveArithmetic.bitLength (longKey h) = h + 1 ∧
      ([longKey h].dedup).length = 1 ∧
      (insertRun (longKey h) true (Search.PositiveTrie.empty false)).2 = (h + 1, h + 1) ∧
      (lookupRun (longKey h)
        (insertRun (longKey h) true (Search.PositiveTrie.empty false)).1).2 = (h + 1, 0) :=
  ⟨longKey_numeric h, longKey_bitLength h, longKey_single_distinct h,
    longKey_empty_insert false true h, longKey_populated_lookup false true h⟩

theorem singleton_long_nodes (h : Nat) :
    (insertRun (longKey h) true (Search.PositiveTrie.empty false)).1.2.numNodes = h + 1 :=
  longKey_insert_numNodes false true h

theorem no_uniform_singleton_bound (bound : Nat) :
    ∃ key : PosNum, ([key].dedup).length = 1 ∧
      bound < (lookupRun key (insertRun key true (Search.PositiveTrie.empty false)).1).2.1 :=
  singleton_lookup_unbounded bound

theorem constant_source_increment (counter : Nat) :
    (incrementRun counter).1 = 1 + counter ∧ counterCalls (incrementRun counter).2 = 2 := by
  refine ⟨incrementRun_value counter, ?_⟩
  rw [incrementRun_cost]
  rfl

theorem collision_empty : collisionsRun [] = (0, ((0, 0), (0, (0, 1)))) := rfl

theorem collision_empty_arbitrary (counter : Nat) (table : Search.PositiveTrie.Table Bool) :
    collisionRun [] (counter, table) = ((counter, table), ((0, 0), (0, (0, 1)))) :=
  collisionRun_nil _

theorem shortest_collision : collisionsRun [1] = (0, ((2, 1), (0, (1, 1)))) := rfl

theorem duplicate_ten : collisionsRun [10, 10] = (1, ((9, 4), (2, (2, 1)))) := by
  apply Prod.ext
  · rw [collisionsRun_value]
    decide
  · rfl

theorem four_equal_tens : collisionsRun [10, 10, 10, 10] =
    (3, ((17, 4), (6, (4, 1)))) := by
  apply Prod.ext
  · rw [collisionsRun_value]
    decide
  · rfl

theorem fresh_only : collisionsRun [1, 2, 3] = (0, ((10, 5), (0, (3, 1)))) := by
  apply Prod.ext
  · rw [collisionsRun_value]
    decide
  · rfl

theorem five_inputs : collisionsRun [3, 1, 4, 1, 5] = (1, ((17, 9), (2, (5, 1)))) := by
  apply Prod.ext
  · rw [collisionsRun_value]
    decide
  · rfl

theorem five_inputs_envelope :
    calls (collisionsRun [3, 1, 4, 1, 5]).2 ≤ 20 ∧
      constructions (collisionsRun [3, 1, 4, 1, 5]).2 ≤ 10 := by
  constructor
  · rw [collisionsRun_cost]
    exact collisionRun_calls_le [3, 1, 4, 1, 5] (0, Search.PositiveTrie.empty false)
  · rw [collisionsRun_cost]
    exact collisionRun_constructions_le [3, 1, 4, 1, 5] (0, Search.PositiveTrie.empty false)

theorem five_inputs_counter_work : counterCalls (collisionsRun [3, 1, 4, 1, 5]).2 = 2 := by
  rw [collisionsRun_counterCalls]
  decide

theorem true_default_all_hits : collisionRun [10, 10] (7, Search.PositiveTrie.empty true) =
    ((9, Search.PositiveTrie.empty true), ((2, 0), (4, (2, 1)))) := rfl

theorem exact_client_overhead (keys : List PosNum) (counter : Nat)
    (table : Search.PositiveTrie.Table Bool) :
    loopSteps (collisionRun keys (counter, table)).2 = keys.length ∧
      terminalCalls (collisionRun keys (counter, table)).2 = 1 :=
  ⟨collisionRun_loopSteps keys _, collisionRun_terminalCalls keys _⟩

theorem ten_logarithmic_bound :
    (lookupRun 10 PositiveTries.threeTenTable).2.1 ≤ 4 :=
  lookupRun_calls_le_log 10 PositiveTries.threeTenTable

theorem source_pi_work : collisionsRun [3, 1, 4, 1, 5, 9, 2, 6] =
    (1, ((35, 18), (2, (8, 1)))) := by
  apply Prod.ext
  · rw [collisionsRun_value]
    decide
  · rfl

theorem source_pi_totalWork : totalWork (collisionsRun [3, 1, 4, 1, 5, 9, 2, 6]).2 = 64 := by
  rw [source_pi_work]
  rfl

theorem source_pi_totalWork_envelope :
    totalWork (collisionsRun [3, 1, 4, 1, 5, 9, 2, 6]).2 ≤ 82 :=
  collisionsRun_totalWork_le [3, 1, 4, 1, 5, 9, 2, 6]

theorem source_pi_bounded_bits :
    totalWork (collisionsRun [3, 1, 4, 1, 5, 9, 2, 6]).2 ≤ 121 := by
  apply collisionsRun_totalWork_le_of_bitLength_le [3, 1, 4, 1, 5, 9, 2, 6] 4
  intro key member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Examples.PositiveTrieWork
