import Examples.OrderedTreeDeletion
import Applications.Search.OrderedTree.Refinement

/-!
# Strict-list equations and real refinement consumers

Frozen cases G09–G12 and G14–G17 retain the weak insertion-prefix boundary,
mixed histories, information loss, independent flag invariant, and actual
independent-universe set/map clients. Lifting adapters here are bounded to
these clients and reuse the existing executors and observers.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.OrderedSetRefinement
open BinaryTree
open Search
open Search.OrderedTree
open Examples.TreeJoin

theorem list_insert_cases :
    [OrderedList.insert 2 [], OrderedList.insert 2 [1, 3, 5],
      OrderedList.insert 3 [1, 3, 5], OrderedList.insert 6 [1, 3, 5],
      OrderedList.insert 1 [1, 1], OrderedList.insert 1 [3, 1]] =
    [[2], [1, 2, 3, 5], [1, 3, 5], [1, 3, 5, 6], [1, 1], [1, 3, 1]] := by decide

theorem list_delete_cases :
    [OrderedList.delete 2 [], OrderedList.delete 3 [1, 3, 5],
      OrderedList.delete 4 [1, 3, 5], OrderedList.delete 1 [3, 1, 2],
      OrderedList.delete 1 [1, 1], OrderedList.delete 1 [3, 1, 1],
      OrderedList.delete 2 [1, 1, 2, 3, 3]] =
    [[], [1, 5], [1, 3, 5], [3, 2], [1], [3, 1], [1, 1, 3, 3]] := by decide

theorem strict_cases :
    OrderedList.Strict ([] : List Nat) ∧ OrderedList.Strict [1] ∧
    OrderedList.Strict [1, 3, 5] ∧ ¬ OrderedList.Strict [1, 1] ∧
    ¬ OrderedList.Strict [2, 1] ∧ ([1, 1] : List Nat).Pairwise (· ≤ ·) := by
  norm_num [OrderedList.Strict]

theorem midpoint_cases :
    OrderedList.Strict ([1, 3] ++ 5 :: [7]) ∧ OrderedList.Strict ([1, 3] ++ [5]) ∧
    OrderedList.Strict [5, 7] ∧ ¬ OrderedList.Strict ([1, 3] ++ 3 :: [4]) ∧
    ¬ OrderedList.Strict ([1, 3] ++ [3]) ∧ OrderedList.Strict [3, 4] := by
  norm_num [OrderedList.Strict]

theorem four_part_cases :
    OrderedList.Strict (1 :: ([3] ++ 5 :: [7])) ∧
    OrderedList.Strict [1, 3] ∧ (1 : Nat) < 5 ∧ OrderedList.Strict [3, 5] ∧
    OrderedList.Strict [5, 7] ∧
    OrderedList.Strict ([3] : List Nat) ∧ OrderedList.Strict ([2] : List Nat) ∧
    OrderedList.Strict [2, 4] ∧ ¬ (3 : Nat) < 2 ∧ ¬ OrderedList.Strict [3, 2, 4] := by
  norm_num [OrderedList.Strict]

theorem cons_snoc_boundaries :
    OrderedList.Strict ([1, 3] : List Nat) ∧
    ¬ OrderedList.Strict (2 :: [1, 3]) ∧ ¬ OrderedList.Strict ([1, 3] ++ [2]) ∧
    OrderedList.Strict ([] : List Nat) ∧ OrderedList.Strict [2] := by
  norm_num [OrderedList.Strict]

theorem insertion_weak_prefix :
    OrderedList.Strict ([1, 3] : List Nat) ∧ ¬ OrderedList.Strict [1, 3, 0, 0] ∧
    [2, 3, 4].map (fun x => OrderedList.insert x [1, 3, 0, 0]) =
      [[1, 2, 3, 0, 0], [1, 3, 0, 0], [1, 3, 0, 0, 4]] := by
  refine ⟨by norm_num [OrderedList.Strict], by norm_num [OrderedList.Strict], by decide⟩

theorem insertion_weak_prefix_consumer (x : Nat) :
    OrderedList.insert x ([1] ++ 3 :: [0, 0]) =
      if x < 3 then OrderedList.insert x [1] ++ 3 :: [0, 0]
      else [1] ++ OrderedList.insert x (3 :: [0, 0]) :=
  OrderedList.insert_distribution x 3 [1] [0, 0] (by norm_num [OrderedList.Strict])

theorem insertion_bad_prefix :
    OrderedList.insert 2 [3, 1] = [2, 3, 1] ∧
    ([3] ++ OrderedList.insert 2 [1]) = [3, 1, 2] ∧
    ¬ OrderedList.Strict ([3, 1] : List Nat) :=
  ⟨by decide, by decide, by norm_num [OrderedList.Strict]⟩

theorem deletion_whole_cases :
    [3, 4, 5, 7].map (fun x => OrderedList.delete x [1, 3, 5, 7, 9]) =
      [[1, 5, 7, 9], [1, 3, 5, 7, 9], [1, 3, 7, 9], [1, 3, 5, 9]] := by decide

theorem deletion_whole_consumer (x : Nat) :
    OrderedList.delete x ([1, 3] ++ 5 :: [7, 9]) =
      if x < 5 then OrderedList.delete x [1, 3] ++ 5 :: [7, 9]
      else [1, 3] ++ OrderedList.delete x (5 :: [7, 9]) :=
  OrderedList.delete_distribution x 5 [1, 3] [7, 9] (by norm_num [OrderedList.Strict])

theorem deletion_weak_premise_fails :
    OrderedList.Strict ([3] : List Nat) ∧
    OrderedList.delete 1 [3, 1] = [3] ∧
    (OrderedList.delete 1 [] ++ [3, 1]) = [3, 1] ∧
    ¬ OrderedList.Strict ([3, 1] : List Nat) :=
  ⟨by norm_num [OrderedList.Strict], by decide, by decide, by norm_num [OrderedList.Strict]⟩

theorem malformed_refinement_boundaries :
    Trees.inorder (insert 3 malformed) = [5, 2, 3] ∧
    OrderedList.insert 3 (Trees.inorder malformed) = [3, 5, 2] ∧
    Trees.inorder (delete 5 malformed) = [5, 2] ∧
    Trees.inorder (deleteJoin 5 malformed) = [5, 2] ∧
    OrderedList.delete 5 (Trees.inorder malformed) = [2] ∧
    member 5 malformed = false ∧ (5 : Nat) ∈ Trees.inorder malformed := by decide

def mixedWord : List (AbstractSet.Update Nat) :=
  [.insert 2, .insert 1, .insert 3, .insert 2, .delete 2, .insert 2,
    .delete 1, .delete 9, .delete 3, .delete 2]

def successorPrefixes : List (BinaryTree Nat) :=
  (List.range 11).map (fun n => AbstractSet.execute deleteOps (mixedWord.take n) .nil)

def joinPrefixes : List (BinaryTree Nat) :=
  (List.range 11).map (fun n => AbstractSet.execute deleteJoinOps (mixedWord.take n) .nil)

theorem successor_prefix_shapes : successorPrefixes =
    [.nil, leaf 2, .node 2 (leaf 1) .nil, aTree, aTree, .node 3 (leaf 1) .nil,
      .node 3 (.node 1 .nil (leaf 2)) .nil, .node 3 (leaf 2) .nil,
      .node 3 (leaf 2) .nil, leaf 2, .nil] := by decide

theorem join_prefix_shapes : joinPrefixes =
    [.nil, leaf 2, .node 2 (leaf 1) .nil, aTree, aTree, .node 1 .nil (leaf 3),
      .node 1 .nil (.node 3 (leaf 2) .nil), .node 3 (leaf 2) .nil,
      .node 3 (leaf 2) .nil, leaf 2, .nil] := by decide

def expectedHistory : List (List Nat × Nat × Nat) :=
  [([], 0, 0), ([2], 1, 1), ([1, 2], 2, 2), ([1, 2, 3], 3, 2), ([1, 2, 3], 3, 2),
    ([1, 3], 2, 2), ([1, 2, 3], 3, 3), ([2, 3], 2, 2), ([2, 3], 2, 2), ([2], 1, 1), ([], 0, 0)]

theorem mixed_prefix_observations :
    successorPrefixes.map (fun t => (Trees.inorder t, t.numNodes, t.height)) = expectedHistory ∧
    joinPrefixes.map (fun t => (Trees.inorder t, t.numNodes, t.height)) = expectedHistory := by decide

theorem every_mixed_prefix_valid (updates : List (AbstractSet.Update Nat)) (n : Nat) :
    Ordered (AbstractSet.execute deleteOps (updates.take n) .nil) ∧
    Ordered (AbstractSet.execute deleteJoinOps (updates.take n) .nil) :=
  ⟨delete_set_laws.prefix_valid updates n ordered_nil,
    refined_deleteJoin_set_laws.prefix_valid updates n ordered_nil⟩

theorem every_mixed_word_meaning (updates : List (AbstractSet.Update Nat)) :
    Trees.setTree (AbstractSet.execute deleteOps updates .nil) =
      updates.foldl AbstractSet.meaningStep (fun _ => False) ∧
    Trees.setTree (AbstractSet.execute deleteJoinOps updates .nil) =
      updates.foldl AbstractSet.meaningStep (fun _ => False) :=
  ⟨delete_set_laws.execute_from_empty updates, refined_deleteJoin_set_laws.execute_from_empty updates⟩

theorem every_mixed_word_refines (updates : List (AbstractSet.Update Nat)) :
    Trees.inorder (AbstractSet.execute deleteOps updates .nil) =
      AbstractSet.execute OrderedList.ops updates [] ∧
    Trees.inorder (AbstractSet.execute deleteJoinOps updates .nil) =
      AbstractSet.execute OrderedList.ops updates [] :=
  ⟨inorder_refinement.execute_from_empty OrderedList.laws updates,
    inorder_join_refinement.execute_from_empty OrderedList.laws updates⟩

theorem shape_and_work_loss :
    aTree ≠ rightThree ∧ Trees.inorder aTree = Trees.inorder rightThree ∧
    aTree.height = 2 ∧ rightThree.height = 3 ∧
    memberRun 2 aTree = (true, 2) ∧ memberRun 2 rightThree = (true, 4) := by decide

theorem set_order_loss (x : Nat) : x ∈ [1, 2] ↔ x ∈ [2, 1] := by
  simp [or_comm]

theorem set_multiplicity_loss (x : Nat) : x ∈ [1] ↔ x ∈ [1, 1] := by simp

def flagOps : AbstractSet.DeleteOps Nat (BinaryTree Nat × Bool) where
  empty := (.nil, true)
  insert x s := (insert x s.1, s.2)
  member x s := member x s.1
  delete x s := (delete x s.1, s.2)

def flagView (s : BinaryTree Nat × Bool) : List Nat := Trees.inorder s.1
def FlagAux (s : BinaryTree Nat × Bool) : Prop := s.2 = true

theorem flag_refinement : AbstractSet.Refinement flagOps OrderedList.ops flagView FlagAux OrderedList.Strict where
  empty := rfl
  auxiliary_empty := rfl
  insert x _ _ hs := inorder_insert x hs
  auxiliary_insert _ _ ha _ := ha
  delete x _ _ hs := inorder_delete x hs
  auxiliary_delete _ _ ha _ := ha
  member x _ _ hs := member_inorder x hs

theorem flag_laws : AbstractSet.DeleteLaws flagOps (fun s x => x ∈ flagView s)
    (AbstractSet.Refinement.Valid flagView FlagAux OrderedList.Strict) :=
  flag_refinement.laws OrderedList.laws

theorem flag_separation :
    flagView (aTree, true) = flagView (aTree, false) ∧
    AbstractSet.Refinement.Valid flagView FlagAux OrderedList.Strict (aTree, true) ∧
    ¬ AbstractSet.Refinement.Valid flagView FlagAux OrderedList.Strict (aTree, false) := by
  refine ⟨rfl, ⟨rfl, (ordered_iff_inorder_pairwise aTree).mp aTree_ordered⟩, ?_⟩
  intro h
  cases h.1

abbrev LiftedSet : Type 1 := ULift.{1} (ValidTree Nat)

def liftedSetOps : AbstractSet.DeleteOps Nat LiftedSet where
  empty := ⟨validDeleteOps.empty⟩
  insert x s := ⟨validDeleteOps.insert x s.down⟩
  member x s := validDeleteOps.member x s.down
  delete x s := ⟨validDeleteOps.delete x s.down⟩

def liftedSetObserve (s : LiftedSet) : Nat → Prop := Trees.setTree s.down.1

theorem liftedSetOps_laws : AbstractSet.DeleteLaws liftedSetOps liftedSetObserve (fun _ => True) where
  empty_valid := trivial
  empty x := validDeleteOps_laws.empty x
  insert_valid _ _ _ := trivial
  insert x s _ y := validDeleteOps_laws.insert x s.down trivial y
  member x s _ := validDeleteOps_laws.member x s.down trivial
  delete_valid _ _ _ := trivial
  delete x s _ y := validDeleteOps_laws.delete x s.down trivial y

theorem lifted_set_recovery (x : Nat) (s : LiftedSet) :
    liftedSetOps.empty.down = validDeleteOps.empty ∧
    (liftedSetOps.insert x s).down = validDeleteOps.insert x s.down ∧
    (liftedSetOps.delete x s).down = validDeleteOps.delete x s.down ∧
    liftedSetOps.member x s = validDeleteOps.member x s.down ∧
    liftedSetObserve s = Trees.setTree s.down.1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lifted_set_execution (updates : List (AbstractSet.Update Nat)) (s : LiftedSet) :
    (AbstractSet.execute liftedSetOps updates s).down =
      AbstractSet.execute validDeleteOps updates s.down := by
  apply SquareKit.ListFusion.foldl_reachable (AbstractSet.step liftedSetOps)
    (AbstractSet.step validDeleteOps) ULift.down (fun _ => True) s trivial
  · exact fun _ _ _ => trivial
  · intro q update _
    cases update <;> rfl

theorem lifted_set_mixed_meaning (updates : List (AbstractSet.Update Nat)) (s : LiftedSet) :
    liftedSetObserve (AbstractSet.execute liftedSetOps updates s) =
      updates.foldl AbstractSet.meaningStep (liftedSetObserve s) :=
  liftedSetOps_laws.execute_observe updates trivial

theorem lifted_set_prefix_ordered (updates : List (AbstractSet.Update Nat)) (n : Nat) (s : LiftedSet) :
    Ordered (AbstractSet.execute liftedSetOps (updates.take n) s).down.1 :=
  (AbstractSet.execute liftedSetOps (updates.take n) s).down.2

abbrev HighPayload : Type 1 := ULift.{1} Nat
abbrev HighMap : Type 2 := ULift.{2} (OrderedMap.Tree Nat HighPayload)

def liftMapOps (base : OrderedMap.DeleteOps Nat HighPayload (OrderedMap.Tree Nat HighPayload)) :
    OrderedMap.DeleteOps Nat HighPayload HighMap where
  empty := ⟨base.empty⟩
  bind key value s := ⟨base.bind key value s.down⟩
  lookup key s := base.lookup key s.down
  delete key s := ⟨base.delete key s.down⟩

def liftMapObserve (s : HighMap) : OrderedMap.Meaning Nat HighPayload := OrderedMap.decode s.down

theorem liftMapOps_laws (base : OrderedMap.DeleteOps Nat HighPayload (OrderedMap.Tree Nat HighPayload))
    (h : OrderedMap.DeleteLaws base OrderedMap.decode) :
    OrderedMap.DeleteLaws (liftMapOps base) liftMapObserve where
  empty := h.empty
  bind key value s := h.bind key value s.down
  lookup key s := h.lookup key s.down
  delete key s := h.delete key s.down

theorem lifted_map_recovery
    (base : OrderedMap.DeleteOps Nat HighPayload (OrderedMap.Tree Nat HighPayload))
    (key : Nat) (value : HighPayload) (s : HighMap) :
    (liftMapOps base).empty.down = base.empty ∧
    ((liftMapOps base).bind key value s).down = base.bind key value s.down ∧
    ((liftMapOps base).delete key s).down = base.delete key s.down ∧
    (liftMapOps base).lookup key s = base.lookup key s.down ∧
    liftMapObserve s = OrderedMap.decode s.down := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lifted_map_consumers (query key : Nat) (value : HighPayload) (s : HighMap) :
    let d := liftMapOps (OrderedMap.deleteTrees Nat HighPayload)
    let j := liftMapOps (OrderedMap.deleteJoinTrees Nat HighPayload)
    d.lookup query (d.delete key (d.bind query value s)) =
      (if query = key then none else some value) ∧
    j.lookup query (j.delete key (j.bind query value s)) =
      (if query = key then none else some value) :=
  ⟨(liftMapOps_laws _ OrderedMap.deleteTrees_laws).lookup_delete_bind query key value s,
    (liftMapOps_laws _ OrderedMap.deleteJoinTrees_laws).lookup_delete_bind query key value s⟩

theorem lifted_projected_bindAll (bindings : List (Nat × HighPayload)) (s : HighMap) (query : Nat) :
    let d := liftMapOps (OrderedMap.deleteTrees Nat HighPayload)
    let j := liftMapOps (OrderedMap.deleteJoinTrees Nat HighPayload)
    d.lookup query (OrderedMap.bindAll d.toOps bindings s) =
      OrderedMap.writeAll bindings (liftMapObserve s) query ∧
    j.lookup query (OrderedMap.bindAll j.toOps bindings s) =
      OrderedMap.writeAll bindings (liftMapObserve s) query :=
  ⟨(liftMapOps_laws _ OrderedMap.deleteTrees_laws).toLaws.lookup_bindAll bindings s query,
    (liftMapOps_laws _ OrderedMap.deleteJoinTrees_laws).toLaws.lookup_bindAll bindings s query⟩

theorem lifted_set_word_finishes_empty :
    (AbstractSet.execute liftedSetOps mixedWord liftedSetOps.empty).down.1 = .nil := by decide

#eval [2, 3, 4].map (fun x => OrderedList.insert x [1, 3, 0, 0])
#eval [3, 4, 5, 7].map (fun x => OrderedList.delete x [1, 3, 5, 7, 9])
#eval successorPrefixes.map (fun t => (Trees.inorder t, t.numNodes, t.height))
#eval joinPrefixes.map (fun t => (Trees.inorder t, t.numNodes, t.height))
#eval (memberRun 2 aTree, memberRun 2 rightThree)
#eval let ops := liftMapOps (OrderedMap.deleteTrees Nat HighPayload)
  ((ops.lookup 4 (ops.delete 7 (ops.bind 4 ⟨9⟩ ops.empty))).map ULift.down,
   (ops.lookup 4 (ops.delete 4 (ops.bind 4 ⟨9⟩ ops.empty))).map ULift.down)
#eval let ops := liftMapOps (OrderedMap.deleteJoinTrees Nat HighPayload)
  ((ops.lookup 4 (ops.delete 7 (ops.bind 4 ⟨9⟩ ops.empty))).map ULift.down,
   (ops.lookup 4 (ops.delete 4 (ops.bind 4 ⟨9⟩ ops.empty))).map ULift.down)

end Examples.OrderedSetRefinement
