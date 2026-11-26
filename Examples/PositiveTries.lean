import Applications.Search.PositiveTrie.Models

/-!
# Positive trie operations, shifted maps and word behavior

The source writes ten and then three. These examples retain its exact raw
constructor result as well as its positive and natural-key observations.
Additional cases distinguish raw shape, defaults, materialized fillers and
explicit writes, including payload types above the lowest universe.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveTries

open Search.PositiveTrie
open Numerals.PositiveKeys

universe u

def threeTenTable : Table Bool := insert 3 true (insert 10 true (empty false))

theorem threeTenTable_constructor : threeTenTable =
    (false, BinaryTree.node false
      (.node false .nil (.node false (.node true .nil .nil) .nil))
      (.node true .nil .nil)) := rfl

theorem threeTenTable_queries : [3, 1, 4, 1, 5].map (fun key : PosNum => lookup key threeTenTable) =
    [true, false, false, false, false] := rfl

theorem threeTenTable_lookup_ten : lookup 10 threeTenTable = true := by
  calc
    lookup 10 threeTenTable = lookup 10 (insert 10 true (empty false)) :=
      lookup_insert_other 3 10 true _ (by decide)
    _ = true := lookup_insert_same 10 true _

theorem threeTenTable_lookup_three : lookup 3 threeTenTable = true :=
  lookup_insert_same 3 true _

/-- Complete the source sanity check using its two relation-preserving writes. -/
theorem abs_threeTenTable : Abs threeTenTable
    (Function.update (Function.update (fun _ : Nat => false) 9 true) 2 true) := by
  have ten := insert_relate (10 : PosNum) true (empty false) (fun _ : Nat => false)
    (empty_isTrie false) (empty_relate false)
  have both := insert_relate (3 : PosNum) true (insert 10 true (empty false))
    (Function.update (fun _ : Nat => false) 9 true)
    (insert_isTrie 10 true (empty false) (empty_isTrie false)) ten
  exact both

theorem threeTenTable_nat_queries : [0, 1, 2, 3, 9, 10].map (abstract threeTenTable) =
    [false, false, true, false, true, false] := rfl

theorem threeTenTable_relate_query : lookup 10 threeTenTable =
    (Function.update (Function.update (fun _ : Nat => false) 9 true) 2 true) 9 :=
  lookup_relate 10 threeTenTable _ trivial abs_threeTenTable

/-- Existing square composition executes the same two writes from empty. -/
theorem threeTenTable_composed_squares : abstract threeTenTable =
    Function.update (Function.update (fun _ : Nat => false) 9 true) 2 true :=
  (Squares.compose (insertSquare 3 true)
    (Squares.compose (insertSquare 10 true) (emptySquare false))).commutes PUnit.unit

theorem lookup_after_composed_squares : lookup 10 threeTenTable = true :=
  (Squares.compose (lookupSquare 10)
    (Squares.compose (insertSquare 3 true)
      (Squares.compose (insertSquare 10 true) (emptySquare false)))).commutes PUnit.unit

theorem overwrite_ten_preserves_three :
    lookup 10 (insert 10 false threeTenTable) = false ∧
      lookup 3 (insert 10 false threeTenTable) = true :=
  ⟨lookup_insert_same 10 false threeTenTable,
    (lookup_insert_other 10 3 false threeTenTable (by decide)).trans threeTenTable_lookup_three⟩

theorem root_overwrite_keeps_children :
    insert 1 true threeTenTable =
      (false, BinaryTree.node true
        (.node false .nil (.node false (.node true .nil .nil) .nil))
        (.node true .nil .nil)) := rfl

theorem string_overwrite : lookup 5 (insert 5 "new" (insert 5 "old" (empty "missing"))) =
    "new" := lookup_insert_same 5 "new" _

theorem string_other_key : lookup 3 (insert 5 "new" (insert 3 "kept" (empty "missing"))) =
    "kept" :=
  (lookup_insert_other 5 3 "new" _ (by decide)).trans (lookup_insert_same 3 "kept" _)

theorem raw_default_differs_from_empty_default :
    (ops (0 : Nat)).get 1 ((ops 0).set 2 9 (77, .nil)) = 77 ∧
      (ops (0 : Nat)).get 2 ((ops 0).set 2 9 (77, .nil)) = 9 ∧
      ((ops (0 : Nat)).set 2 9 (77, .nil)).1 = 77 :=
  ⟨(laws 0).get_set_other 2 1 9 (77, .nil) (by decide) trivial,
    (laws 0).get_set_same 2 9 (77, .nil) trivial, rfl⟩

theorem higher_universe_payloads (default value : Type u) :
    (insert 2 value (empty default)).1 = default ∧
      lookup 2 (insert 2 value (empty default)) = value ∧
      lookup 1 (insert 2 value (empty default)) = default :=
  ⟨insert_default 2 value (empty default), lookup_insert_same 2 value (empty default), rfl⟩

theorem higher_universe_meaning (default value : Type u) :
    abstract (insert 2 value (empty default)) =
      Function.update (fun _ : Nat => default) 1 value := by
  rw [abstract_insert, abstract_empty]
  rfl

theorem repeated_write_meaning :
    abstract (insert 5 51 (insert 5 50 (empty (7 : Nat)))) =
      Function.update (fun _ : Nat => 7) 4 51 := by
  rw [abstract_insert_shadow, abstract_insert, abstract_empty]
  rfl

theorem self_write_meaning : abstract (insert 10 (lookup 10 threeTenTable) threeTenTable) =
    abstract threeTenTable := abstract_insert_self 10 threeTenTable

theorem distinct_writes_commute :
    abstract (insert 3 "three" (insert 10 "ten" (empty "missing"))) =
      abstract (insert 10 "ten" (insert 3 "three" (empty "missing"))) :=
  abstract_insert_comm 10 3 "ten" "three" (empty "missing") (by decide)

theorem repeated_history_observation :
    Search.TotalTable.observe (ops (7 : Nat))
      (Search.TotalTable.setAll (ops 7) [(2, 20), (3, 30), (2, 22)] (empty 7)) =
    Function.update
      (Function.update (Function.update (fun _ : PosNum => 7) 2 20) 3 30) 2 22 := by
  have initially : Search.TotalTable.observe (ops (7 : Nat)) (empty 7) =
      (fun _ : PosNum => 7) := by
    funext key
    exact lookup_empty 7 key
  simpa only [List.foldl, initially] using
    (observe_setAll (7 : Nat) [(2, 20), (3, 30), (2, 22)] (empty 7))

theorem repeated_history_queries :
    [1, 2, 3, 4].map (fun key : PosNum => lookup key
      (Search.TotalTable.setAll (ops (7 : Nat)) [(2, 20), (3, 30), (2, 22)] (empty 7))) =
    [7, 22, 30, 7] := rfl

/-- Equal total observations do not identify the raw representation. -/
theorem default_write_same_observation :
    abstract (insert 1 11 (empty (11 : Nat))) = abstract (empty 11) :=
  abstract_insert_self 1 (empty 11)

theorem default_write_different_raw_tree :
    (insert 1 11 (empty (11 : Nat))).2 ≠ (empty (11 : Nat)).2 := by
  decide

theorem default_write_different_raw_table :
    insert 1 11 (empty (11 : Nat)) ≠ empty 11 := by
  intro same
  exact default_write_different_raw_tree (congrArg Prod.snd same)

/-- Key one is a materialized filler although the explicit history only writes two. -/
theorem filler_is_not_explicit_write :
    BinaryTree.get 1
      (Search.TotalTable.setAll (ops (77 : Nat)) [(2, 9)] (empty 77)).2 = some 77 ∧
    (1 : PosNum) ∉ ([(2, 9)] : List (PosNum × Nat)).map Prod.fst :=
  ⟨rfl, by decide⟩

theorem raw_shared_default_is_necessary :
    look (20 : Nat) 1 (ins 10 2 30 .nil) = 10 ∧
      look (20 : Nat) 1 .nil = 20 ∧
      look (20 : Nat) 1 (ins 10 2 30 .nil) ≠ look (20 : Nat) 1 .nil :=
  ⟨rfl, rfl, by decide⟩

/-- The source's Goal 419 identifies positive ten by its binary constructors. -/
theorem ten_constructor : (10 : PosNum) = .bit0 (.bit1 (.bit0 .one)) := rfl

theorem ten_word : word (10 : PosNum) = [false, true, false] := rfl

theorem one_stops_at_root : word (1 : PosNum) = [] ∧
    SquareKit.WordCoalgebra.run (coalgebra false) threeTenTable.2 [] = false := ⟨rfl, rfl⟩

theorem ten_word_lookup :
    SquareKit.WordCoalgebra.run (coalgebra false) threeTenTable.2 [false, true, false] = true :=
  (run_word false 10 threeTenTable.2).trans threeTenTable_lookup_ten

theorem nil_absorbs_unused_suffix :
    SquareKit.WordCoalgebra.run (coalgebra "missing") .nil
      [true, false, true, true, false] = "missing" := run_leaf _ _

theorem snapshot_ten :
    (SquareKit.WordCoalgebra.unfold (coalgebra false) threeTenTable.2 3).lookup
      [false, true, false] = some true := by
  exact (lookup_unfold_word false 10 threeTenTable.2 3 (by decide)).trans
    (congrArg some threeTenTable_lookup_ten)

theorem source_tree_reachable_finite :
    (Set.range (fun bits : List Bool => bits.foldl next threeTenTable.2)).Finite :=
  reachable_finite threeTenTable.2

theorem ten_reaches_written_node :
    [false, true, false].foldl next threeTenTable.2 = BinaryTree.node true .nil .nil := rfl

theorem beyond_ten_reaches_nil :
    [false, true, false, true, false].foldl next threeTenTable.2 = .nil := rfl

end Examples.PositiveTries
