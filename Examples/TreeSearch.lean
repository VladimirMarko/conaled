import Applications.Resources.TreeSearch
import Examples.OrderedTrees
import Mathlib.Data.Tree.Get
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Order.Compare
import Mathlib.Tactic.NormNum

/-! Connected selected-path search applications. The expected printed-tree,
false-payload, duplicate, malformed and finite present-query calculations were
recorded before implementation. Source/model and statement assessment:
`docs/research/fdsa-tree-search.md`. Counts concern the declared search model;
the existing indexOf/get connection below concerns values only. -/
set_option autoImplicit false
set_option warningAsError true

namespace TreeSearchExamples
universe u v w x
variable {α : Type u} {β : Type v} {κ : Type w} {γ : Type x}
open Resources.TreeSearch
open OrderedTreeExamples

/-- The book's literal comparator uses the existing agreement theorem.
This compares complete measured query runs, with comparator internals uncharged. -/
theorem source_run_eq_cmp [LinearOrder κ] (key : α → κ) (q : κ)
    (t : BinaryTree α) :
    run (fun a => compareOfLessAndEq q (key a)) t =
      run (fun a => cmp q (key a)) t :=
  congrArg (fun route : α → Ordering => run route t)
    (funext fun a => (cmp_eq_compareOfLessAndEq q (key a)).symm)

/-- Five actual runs distinguish root/left/right/deep hits and a deep miss. -/
theorem printed_runs :
    ([6, 3, 9, 8, 4] : List Nat).map
        (fun q => run (compareOfLessAndEq q) printedTree) =
      [(some 6, 1), (some 3, 2), (some 9, 2), (some 8, 3), (none, 4)] := rfl

theorem printed_height : printedTree.height = 3 := rfl

/-- Unique semantic keys, but the key 5 is on the wrong side of the root. -/
def malformed : BinaryTree (Nat × String) :=
  .node (2, "root") (TreeRotationExamples.singletonTree (5, "left")) .nil

theorem malformed_inorder : Trees.inorder malformed = [(5, "left"), (2, "root")] := rfl

theorem malformed_keys_distinct : ((Trees.inorder malformed).map Prod.fst).Nodup := by
  rw [malformed_inorder]
  decide

theorem malformed_not_ordered :
    ¬ Trees.Ordered (fun a b : Nat × String => a.1 < b.1) malformed := by
  intro h
  have hp := (Trees.ordered_key_iff_pairwise Prod.fst malformed).1 h
  rw [malformed_inorder] at hp
  exact (by decide : ¬ (([(5, "left"), (2, "root")] : List (Nat × String)).map
    Prod.fst).Pairwise (fun a b => a < b)) hp

/-- This is the actual left rotation of the retained duplicate-key fixture. -/
def duplicateAfter : BinaryTree (Nat × Nat) :=
  .node (1, 20) (TreeRotationExamples.singletonTree (1, 10)) .nil

theorem duplicate_left : Trees.rotateLeft? sameKeyRecords = some duplicateAfter :=
  Trees.rotateLeft?_node_node .nil (1, 10) .nil (1, 20) .nil

theorem duplicate_inorder : Trees.inorder duplicateAfter = Trees.inorder sameKeyRecords :=
  Trees.inorder_of_rotateLeft? sameKeyRecords duplicateAfter duplicate_left

/-- The literal increasing chain in the book's finite present-key comparison. -/
def chain369 : BinaryTree Nat :=
  .node 3 .nil (.node 6 .nil (TreeRotationExamples.singletonTree 9))

theorem chain369_inorder : Trees.inorder chain369 = [3, 6, 9] := rfl

theorem chain369_ordered : Trees.Ordered (fun a b : Nat => a < b) chain369 := by
  apply Trees.ordered_of_pairwise_inorder
  rw [chain369_inorder]
  decide


/-- Empty search has an invocation but no stored-node visit. -/
theorem empty_case (route : α → Ordering) :
    run route (.nil : BinaryTree α) = (none, 1) ∧ visits route .nil = 0 := ⟨rfl, rfl⟩

/-- The key query exists even though the semantic payload type is uninhabited. -/
theorem empty_payload (q : Nat) (t : BinaryTree (Nat × Empty)) :
    t = .nil ∧
      run (fun a : Nat × Empty => compareOfLessAndEq q a.1) t = (none, 1) ∧
      (find? (fun a : Nat × Empty => compareOfLessAndEq q a.1) t).map Prod.snd = none ∧
      visits (fun a : Nat × Empty => compareOfLessAndEq q a.1) t = 0 := by
  cases t with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | node a l r => exact Empty.elim a.2

/-- Both observers consume the actual measured result, without another query. -/
theorem observe_payload (route : κ × β → Ordering) (t : BinaryTree (κ × β)) :
    Resources.bind (run route t) (fun o => Resources.pure (o.map Prod.snd)) =
      ((find? route t).map Prod.snd, entries route t) :=
  Resources.CallCount.primitive_rule (fun o : Option (κ × β) => o.map Prod.snd) (run route t)

theorem observe_presence (route : α → Ordering) (t : BinaryTree α) :
    Resources.bind (run route t) (fun o => Resources.pure o.isSome) =
      ((find? route t).isSome, entries route t) :=
  Resources.CallCount.primitive_rule (fun o : Option α => o.isSome) (run route t)

theorem printed_eight_run : run (compareOfLessAndEq 8) printedTree = (some 8, 3) := rfl

theorem printed_four_run : run (compareOfLessAndEq 4) printedTree = (none, 4) := rfl

theorem printed_after_six_run : run (compareOfLessAndEq 6) printedAfter = (some 6, 2) := rfl

theorem tagged_zero_run :
    run (fun a : Nat × Bool => compareOfLessAndEq 0 a.1) taggedTree = (some (0, false), 2) := rfl

theorem tagged_three_run :
    run (fun a : Nat × Bool => compareOfLessAndEq 3 a.1) taggedTree = (none, 3) := rfl

theorem tagged_payload_zero :
    Resources.bind (run (fun a : Nat × Bool => compareOfLessAndEq 0 a.1) taggedTree)
        (fun o => Resources.pure (o.map Prod.snd)) = (some false, 2) :=
  (observe_payload (fun a : Nat × Bool => compareOfLessAndEq 0 a.1) taggedTree).trans
    (congrArg (fun r : Resources.Measured (Option (Nat × Bool)) Nat => (r.1.map Prod.snd, r.2))
      tagged_zero_run)

theorem tagged_presence_zero :
    Resources.bind (run (fun a : Nat × Bool => compareOfLessAndEq 0 a.1) taggedTree)
        (fun o => Resources.pure o.isSome) = (true, 2) :=
  (observe_presence (fun a : Nat × Bool => compareOfLessAndEq 0 a.1) taggedTree).trans
    (congrArg (fun r : Resources.Measured (Option (Nat × Bool)) Nat => (r.1.isSome, r.2))
      tagged_zero_run)

theorem tagged_payload_three :
    Resources.bind (run (fun a : Nat × Bool => compareOfLessAndEq 3 a.1) taggedTree)
        (fun o => Resources.pure (o.map Prod.snd)) = (none, 3) :=
  (observe_payload (fun a : Nat × Bool => compareOfLessAndEq 3 a.1) taggedTree).trans
    (congrArg (fun r : Resources.Measured (Option (Nat × Bool)) Nat => (r.1.map Prod.snd, r.2))
      tagged_three_run)

theorem tagged_presence_three :
    Resources.bind (run (fun a : Nat × Bool => compareOfLessAndEq 3 a.1) taggedTree)
        (fun o => Resources.pure o.isSome) = (false, 3) :=
  (observe_presence (fun a : Nat × Bool => compareOfLessAndEq 3 a.1) taggedTree).trans
    (congrArg (fun r : Resources.Measured (Option (Nat × Bool)) Nat => (r.1.isSome, r.2))
      tagged_three_run)

theorem malformed_run :
    run (fun a : Nat × String => compareOfLessAndEq 5 a.1) malformed = (none, 2) := rfl

theorem duplicate_before_run :
    run (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) sameKeyRecords = (some (1, 10), 1) := rfl

theorem duplicate_after_run :
    run (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) duplicateAfter = (some (1, 20), 1) := rfl

theorem dishonest_run :
    run (fun _ : Nat => Ordering.eq) (three 1 2 3) = (some 2, 1) := rfl

/-- Each list element is the output and invocation count of an actual query. -/
theorem balanced_present_runs :
    ([3, 6, 9] : List Nat).map
        (fun q => run (compareOfLessAndEq q) (three 3 6 9)) =
      [(some 3, 2), (some 6, 1), (some 9, 2)] := rfl

theorem chain_present_runs :
    ([3, 6, 9] : List Nat).map (fun q => run (compareOfLessAndEq q) chain369) =
      [(some 3, 1), (some 6, 2), (some 9, 3)] := rfl


private theorem visits_of_run_some (route : α → Ordering) (t : BinaryTree α)
    {a : α} {n : Nat} (h : run route t = (some a, n)) : visits route t = n :=
  (entries_eq_visits_of_some route t a (congrArg Prod.fst h)).symm.trans
    (congrArg Prod.snd h)

private theorem visits_of_run_none (route : α → Ordering) (t : BinaryTree α)
    (n : Nat) (h : run route t = (none, n + 1)) : visits route t = n := by
  have he : visits route t + 1 = n + 1 :=
    (entries_eq_visits_add_one_of_none route t (congrArg Prod.fst h)).symm.trans
      (congrArg Prod.snd h)
  exact Nat.add_right_cancel he

/-- Source specialization uses the existing comparison facts at the actual labels. -/
theorem source_find_spec [LinearOrder κ] (key : α → κ) (q : κ)
    (t : BinaryTree α) (h : Trees.Ordered (fun a b => key a < key b) t) (a : α) :
    find? (fun b => compareOfLessAndEq q (key b)) t = some a ↔
      a ∈ Trees.inorder t ∧ key a = q :=
  find?_eq_some_iff key q (fun b => compareOfLessAndEq q (key b)) t h
    (fun b _ => by simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares q (key b)) a

theorem source_none_spec [LinearOrder κ] (key : α → κ) (q : κ)
    (t : BinaryTree α) (h : Trees.Ordered (fun a b => key a < key b) t) :
    find? (fun b => compareOfLessAndEq q (key b)) t = none ↔
      ∀ a ∈ Trees.inorder t, key a ≠ q :=
  find?_eq_none_iff key q (fun b => compareOfLessAndEq q (key b)) t h
    (fun b _ => by simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares q (key b))

theorem source_find_inorder [LinearOrder κ] (key : α → κ) (q : κ)
    (t : BinaryTree α) (h : Trees.Ordered (fun a b => key a < key b) t) :
    find? (fun b => compareOfLessAndEq q (key b)) t =
      (Trees.inorder t).find?
        (fun b => decide (compareOfLessAndEq q (key b) = Ordering.eq)) :=
  find?_eq_find key q (fun b => compareOfLessAndEq q (key b)) t h
    (fun b _ => by simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares q (key b))

/-- The list observer needs only lawful key equality; semantic values remain arbitrary. -/
theorem source_payload_lookup [LinearOrder κ] [BEq κ] [LawfulBEq κ] (q : κ)
    (t : BinaryTree (κ × β)) (h : Trees.Ordered (fun a b => a.1 < b.1) t) :
    (find? (fun a : κ × β => compareOfLessAndEq q a.1) t).map Prod.snd =
      (Trees.inorder t).lookup q :=
  map_find?_eq_lookup q (fun a : κ × β => compareOfLessAndEq q a.1) t h
    (fun a _ => by simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares q a.1)

/-- Existing position search followed by get agrees in value for any decidable relation.
No ordering law or resource correspondence for the two traversals is assumed. -/
theorem find_eq_indexOf_get (lt : α → α → Prop) [DecidableRel lt]
    (q : α) (t : BinaryTree α) :
    find? (fun a => cmpUsing lt q a) t =
      (BinaryTree.indexOf lt q t).bind (fun n => BinaryTree.get n t) := by
  induction t with
  | nil => exact find?_nil _
  | node a l r ihl ihr =>
      cases h : cmpUsing lt q a with
      | lt =>
          rw [find?_node_lt _ a l r h, BinaryTree.indexOf, h, ihl]
          cases BinaryTree.indexOf lt q l <;> rfl
      | eq =>
          rw [find?_node_eq _ a l r h, BinaryTree.indexOf, h] <;> rfl
      | gt =>
          rw [find?_node_gt _ a l r h, BinaryTree.indexOf, h, ihr]
          cases BinaryTree.indexOf lt q r <;> rfl

/-- Erase only the outer annotation, across independent key/value/tag universes. -/
theorem outer_tag_run (route : κ × β → Ordering) (t : BinaryTree ((κ × β) × γ)) :
    run route (t.map Prod.fst) =
      ((run (fun a : (κ × β) × γ => route a.1) t).1.map Prod.fst, (run (fun a : (κ × β) × γ => route a.1) t).2) :=
  run_map_pullback route Prod.fst t

theorem outer_tag_counts (route : κ × β → Ordering) (t : BinaryTree ((κ × β) × γ)) :
    entries route (t.map Prod.fst) = entries (fun a : (κ × β) × γ => route a.1) t ∧
      visits route (t.map Prod.fst) = visits (fun a : (κ × β) × γ => route a.1) t :=
  ⟨entries_map (fun a : (κ × β) × γ => route a.1) route Prod.fst t (fun _ _ => rfl),
    visits_map (fun a : (κ × β) × γ => route a.1) route Prod.fst t (fun _ _ => rfl)⟩

theorem outer_tag_payload (route : κ × β → Ordering)
    (t : BinaryTree ((κ × β) × γ)) :
    (find? route (t.map Prod.fst)).map Prod.snd =
      (find? (fun a : (κ × β) × γ => route a.1) t).map (fun a : (κ × β) × γ => a.1.2) := by
  rw [find?_map (fun a : (κ × β) × γ => route a.1) route Prod.fst t (fun _ _ => rfl)]
  cases find? (fun a : (κ × β) × γ => route a.1) t <;> rfl

theorem outer_tag_observer (route : κ × β → Ordering)
    (t : BinaryTree ((κ × β) × γ)) :
    Resources.bind (run route (t.map Prod.fst)) (fun o => Resources.pure (o.map Prod.snd)) =
      ((find? (fun a : (κ × β) × γ => route a.1) t).map (fun a : (κ × β) × γ => a.1.2),
        entries (fun a : (κ × β) × γ => route a.1) t) := by
  rw [observe_payload, outer_tag_payload, (outer_tag_counts route t).1]

/-- Correctness connects arbitrary query results to the printed inorder observation. -/
theorem printed_find_spec (q a : Nat) :
    find? (compareOfLessAndEq q) printedTree = some a ↔
      a ∈ [2, 3, 5, 6, 8, 9] ∧ a = q := by
  simpa only [printed_inorder] using source_find_spec (fun n : Nat => n) q
    printedTree printed_ordered a

theorem printed_four_absent : find? (compareOfLessAndEq 4) printedTree = none := by
  apply (source_none_spec (fun n : Nat => n) 4 printedTree printed_ordered).2
  simp [printed_inorder]

theorem printed_presence (q : Nat) :
    (find? (compareOfLessAndEq q) printedTree).isSome ↔ q ∈ [2, 3, 5, 6, 8, 9] := by
  have h := find?_isSome_iff (fun n : Nat => n) q (compareOfLessAndEq q)
    printedTree printed_ordered
    (fun a _ => by simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares q a)
  constructor
  · intro hp
    rcases h.mp hp with ⟨a, ha, heq⟩
    simpa only [printed_inorder, heq] using ha
  · intro hq
    apply h.mpr
    exact ⟨q, by simpa only [printed_inorder] using hq, rfl⟩

/-- The exact hit/miss count laws recover visits from these actual run results. -/
theorem printed_visits :
    ([6, 3, 9, 8, 4] : List Nat).map
        (fun q => visits (compareOfLessAndEq q) printedTree) = [1, 2, 2, 3, 3] := by
  change [visits (compareOfLessAndEq 6) printedTree,
    visits (compareOfLessAndEq 3) printedTree, visits (compareOfLessAndEq 9) printedTree,
    visits (compareOfLessAndEq 8) printedTree, visits (compareOfLessAndEq 4) printedTree] = _
  rw [visits_of_run_some _ _ (show run (compareOfLessAndEq 6) printedTree = (some 6, 1) from rfl),
    visits_of_run_some _ _ (show run (compareOfLessAndEq 3) printedTree = (some 3, 2) from rfl),
    visits_of_run_some _ _ (show run (compareOfLessAndEq 9) printedTree = (some 9, 2) from rfl),
    visits_of_run_some _ _ printed_eight_run,
    visits_of_run_none _ _ 3 printed_four_run]

theorem printed_raw_bounds (q : Nat) :
    visits (compareOfLessAndEq q) printedTree ≤ 3 ∧
      entries (compareOfLessAndEq q) printedTree ≤ 4 := by
  constructor
  · simpa only [printed_height] using visits_le_height (compareOfLessAndEq q) printedTree
  · simpa only [printed_height] using entries_le_height_add_one (compareOfLessAndEq q) printedTree

theorem printed_tight_hit_and_miss :
    visits (compareOfLessAndEq 8) printedTree = printedTree.height ∧
      entries (compareOfLessAndEq 8) printedTree = printedTree.height ∧
      entries (compareOfLessAndEq 4) printedTree = printedTree.height + 1 := by
  rw [printed_height]
  exact ⟨visits_of_run_some _ _ printed_eight_run,
    congrArg Prod.snd printed_eight_run, congrArg Prod.snd printed_four_run⟩

/-- The general nonempty theorem supplies a stored witness for this actual tree. -/
theorem printed_deepest_witness :
    ∃ a ∈ Trees.inorder printedTree,
      run (compareOfLessAndEq a) printedTree = (some a, printedTree.height) ∧
        visits (compareOfLessAndEq a) printedTree = printedTree.height :=
  exists_source_run_eq_height (fun n : Nat => n) printedTree (by decide) printed_ordered

/-- Validity and identical inorder preserve all query values, through the first-entry law. -/
theorem printed_rotation_values (q : Nat) :
    find? (compareOfLessAndEq q) printedAfter = find? (compareOfLessAndEq q) printedTree := by
  calc
    _ = (Trees.inorder printedAfter).find?
        (fun a => decide (compareOfLessAndEq q a = Ordering.eq)) :=
      source_find_inorder (fun n : Nat => n) q printedAfter printedAfter_ordered
    _ = (Trees.inorder printedTree).find?
        (fun a => decide (compareOfLessAndEq q a = Ordering.eq)) :=
      congrArg (List.find? (fun a => decide (compareOfLessAndEq q a = Ordering.eq)))
        (Trees.inorder_of_rotateLeft? printedTree printedAfter printed_left)
    _ = _ := (source_find_inorder (fun n : Nat => n) q printedTree printed_ordered).symm

theorem printed_rotation_costs :
    entries (compareOfLessAndEq 6) printedTree = 1 ∧
      visits (compareOfLessAndEq 6) printedTree = 1 ∧
      entries (compareOfLessAndEq 6) printedAfter = 2 ∧
      visits (compareOfLessAndEq 6) printedAfter = 2 :=
  ⟨rfl, visits_of_run_some _ _ (show run (compareOfLessAndEq 6) printedTree = (some 6, 1) from rfl),
    congrArg Prod.snd printed_after_six_run, visits_of_run_some _ _ printed_after_six_run⟩


theorem tagged_lookup (q : Nat) :
    (find? (fun a : Nat × Bool => compareOfLessAndEq q a.1) taggedTree).map Prod.snd =
      (Trees.inorder taggedTree).lookup q :=
  source_payload_lookup q taggedTree taggedTree_ordered

theorem tagged_visits :
    visits (fun a : Nat × Bool => compareOfLessAndEq 0 a.1) taggedTree = 2 ∧
      visits (fun a : Nat × Bool => compareOfLessAndEq 3 a.1) taggedTree = 2 :=
  ⟨visits_of_run_some _ _ tagged_zero_run, visits_of_run_none _ _ 2 tagged_three_run⟩

/-- This map discards the Bool value; key preservation, not global injectivity,
is what makes the selected branches and query observations agree. -/
theorem discard_transport (q : Nat) :
    ¬ Function.Injective discardTag ∧
      run (fun a : Nat × Unit => compareOfLessAndEq q a.1) (taggedTree.map discardTag) =
        ((run (fun a : Nat × Bool => compareOfLessAndEq q a.1) taggedTree).1.map discardTag,
          (run (fun a : Nat × Bool => compareOfLessAndEq q a.1) taggedTree).2) := by
  refine ⟨discardTag_not_injective, ?_⟩
  apply run_map
  intro a _
  rw [discardTag_preserves_key]

theorem discard_zero_run :
    run (fun a : Nat × Unit => compareOfLessAndEq 0 a.1) (taggedTree.map discardTag) =
      (some (0, ()), 2) := by
  simpa only [tagged_zero_run, Option.map_some, discardTag] using (discard_transport 0).2

theorem discard_three_run :
    run (fun a : Nat × Unit => compareOfLessAndEq 3 a.1) (taggedTree.map discardTag) =
      (none, 3) := by
  simpa only [tagged_three_run, Option.map_none] using (discard_transport 3).2

theorem discard_visits :
    visits (fun a : Nat × Unit => compareOfLessAndEq 0 a.1) (taggedTree.map discardTag) = 2 ∧
      visits (fun a : Nat × Unit => compareOfLessAndEq 3 a.1) (taggedTree.map discardTag) = 2 :=
  ⟨visits_of_run_some _ _ discard_zero_run, visits_of_run_none _ _ 2 discard_three_run⟩

/-- Pruning fails despite unique keys; first-inorder association lookup sees the entry. -/
theorem malformed_failure :
    find? (fun a : Nat × String => compareOfLessAndEq 5 a.1) malformed = none ∧
      visits (fun a : Nat × String => compareOfLessAndEq 5 a.1) malformed = 1 ∧
      (5, "left") ∈ Trees.inorder malformed ∧
      (Trees.inorder malformed).lookup 5 = some "left" :=
  ⟨congrArg Prod.fst malformed_run, visits_of_run_none _ _ 1 malformed_run,
    by simp [malformed_inorder], rfl⟩

theorem malformed_raw_bounds (route : Nat × String → Ordering) :
    visits route malformed ≤ malformed.height ∧
      entries route malformed ≤ malformed.height + 1 :=
  ⟨visits_le_height route malformed, entries_le_height_add_one route malformed⟩

/-- Full-record distinctness and weak key sorting persist through this rotation. -/
theorem duplicate_domains :
    (Trees.inorder sameKeyRecords).Nodup ∧ (Trees.inorder duplicateAfter).Nodup ∧
      ((Trees.inorder sameKeyRecords).map Prod.fst).SortedLE ∧
      ((Trees.inorder duplicateAfter).map Prod.fst).SortedLE ∧
      ¬ Trees.Ordered (fun a b : Nat × Nat => a.1 < b.1) duplicateAfter := by
  have hw : ((Trees.inorder sameKeyRecords).map Prod.fst).SortedLE := by
    apply List.sortedLE_iff_pairwise.mpr
    rw [sameKeyRecords_keys]
    decide
  refine ⟨sameKeyRecords_distinct, ?_, hw, ?_, ?_⟩
  · rw [duplicate_inorder]
    exact sameKeyRecords_distinct
  · rw [duplicate_inorder]
    exact hw
  · intro h
    exact sameKeyRecords_not_key_ordered
      ((Trees.ordered_rotateLeft?_iff (fun a b : Nat × Nat => a.1 < b.1)
        (fun _ _ _ hab hbc => lt_trans hab hbc) sameKeyRecords duplicateAfter duplicate_left).1 h)

theorem duplicate_payloads :
    (find? (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) sameKeyRecords).map Prod.snd = some 10 ∧
      (find? (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) duplicateAfter).map Prod.snd = some 20 ∧
      (Trees.inorder sameKeyRecords).lookup 1 = some 10 ∧
      (Trees.inorder duplicateAfter).lookup 1 = some 10 := by
  refine ⟨congrArg (Option.map Prod.snd) (congrArg Prod.fst duplicate_before_run),
    congrArg (Option.map Prod.snd) (congrArg Prod.fst duplicate_after_run), rfl, ?_⟩
  rw [duplicate_inorder] <;> rfl

theorem duplicate_lookup_disagrees :
    (find? (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) duplicateAfter).map Prod.snd ≠
      (Trees.inorder duplicateAfter).lookup 1 := by
  rw [duplicate_payloads.2.1, duplicate_payloads.2.2.2]
  decide

/-- This failure of payload lookup is not a failure of Boolean membership. -/
theorem duplicate_presence_and_visits :
    (find? (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) sameKeyRecords).isSome = true ∧
      (find? (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) duplicateAfter).isSome = true ∧
      visits (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) sameKeyRecords = 1 ∧
      visits (fun a : Nat × Nat => compareOfLessAndEq 1 a.1) duplicateAfter = 1 :=
  ⟨congrArg Option.isSome (congrArg Prod.fst duplicate_before_run),
    congrArg Option.isSome (congrArg Prod.fst duplicate_after_run),
    visits_of_run_some _ _ duplicate_before_run, visits_of_run_some _ _ duplicate_after_run⟩

theorem dishonest_ordered : Trees.Ordered (fun a b : Nat => a < b) (three 1 2 3) :=
  three_strict_ordered 1 2 3 (by decide) (by decide)

/-- An arbitrary EQ route still returns a stored entry, without key correctness. -/
theorem dishonest_stored : 2 ∈ Trees.inorder (three (1 : Nat) 2 3) :=
  (find?_some_spec (fun _ : Nat => Ordering.eq) (three 1 2 3) 2
    (congrArg Prod.fst dishonest_run)).1

theorem dishonest_calibration_fails :
    ¬ ∀ a ∈ Trees.inorder (three (1 : Nat) 2 3), (Ordering.eq).Compares (9 : Nat) a := by
  intro h
  have he : (2 : Nat) = 9 :=
    key_eq_of_find?_eq_some (fun n : Nat => n) 9 (fun _ => Ordering.eq)
      (three 1 2 3) 2 h (congrArg Prod.fst dishonest_run)
  exact (by decide : (2 : Nat) ≠ 9) he

theorem dishonest_visits : visits (fun _ : Nat => Ordering.eq) (three 1 2 3) = 1 :=
  visits_of_run_some _ _ dishonest_run

/-- One invocation can be an empty miss or a root hit, with different V. -/
theorem entries_do_not_determine_visits :
    entries (fun _ : Nat => Ordering.eq) .nil =
        entries (fun _ : Nat => Ordering.eq) (three 1 2 3) ∧
      visits (fun _ : Nat => Ordering.eq) .nil ≠
        visits (fun _ : Nat => Ordering.eq) (three 1 2 3) := by
  refine ⟨rfl, ?_⟩
  rw [visits_nil, dishonest_visits]
  decide

/-- Project the invocation lists from the complete measured runs. -/
theorem balanced_present_entries :
    ([3, 6, 9] : List Nat).map (fun q => entries (compareOfLessAndEq q) (three 3 6 9)) =
      [2, 1, 2] := by
  simpa only [List.map_map, Function.comp_def, entries, List.map_cons, List.map_nil]
    using congrArg (List.map Prod.snd) balanced_present_runs

theorem chain_present_entries :
    ([3, 6, 9] : List Nat).map (fun q => entries (compareOfLessAndEq q) chain369) =
      [1, 2, 3] := by
  simpa only [List.map_map, Function.comp_def, entries, List.map_cons, List.map_nil]
    using congrArg (List.map Prod.snd) chain_present_runs

/-- These queries are all present: the hit law, not a universal E=V claim,
transports their invocation lists to their visit lists. -/
theorem balanced_present_visits :
    ([3, 6, 9] : List Nat).map (fun q => visits (compareOfLessAndEq q) (three 3 6 9)) =
      [2, 1, 2] := by
  calc
    _ = ([3, 6, 9] : List Nat).map
        (fun q => entries (compareOfLessAndEq q) (three 3 6 9)) := by
      apply List.map_congr_left
      intro q hq
      have hm : q ∈ Trees.inorder (three (3 : Nat) 6 9) := by
        simpa only [three_inorder] using hq
      have ho := three_strict_ordered (3 : Nat) 6 9 (by decide) (by decide)
      have hf := (source_find_spec (fun n : Nat => n) q (three 3 6 9) ho q).2 ⟨hm, rfl⟩
      exact (entries_eq_visits_of_some (compareOfLessAndEq q) (three 3 6 9) q hf).symm
    _ = _ := balanced_present_entries

theorem chain_present_visits :
    ([3, 6, 9] : List Nat).map (fun q => visits (compareOfLessAndEq q) chain369) =
      [1, 2, 3] := by
  calc
    _ = ([3, 6, 9] : List Nat).map
        (fun q => entries (compareOfLessAndEq q) chain369) := by
      apply List.map_congr_left
      intro q hq
      have hm : q ∈ Trees.inorder chain369 := by
        simpa only [chain369_inorder] using hq
      have hf := (source_find_spec (fun n : Nat => n) q chain369 chain369_ordered q).2 ⟨hm, rfl⟩
      exact (entries_eq_visits_of_some (compareOfLessAndEq q) chain369 q hf).symm
    _ = _ := chain_present_entries

theorem present_query_sums :
    (([3, 6, 9] : List Nat).map
      (fun q => entries (compareOfLessAndEq q) (three 3 6 9))).sum = 5 ∧
    (([3, 6, 9] : List Nat).map
      (fun q => entries (compareOfLessAndEq q) chain369)).sum = 6 := by
  rw [balanced_present_entries, chain_present_entries]
  exact ⟨rfl, rfl⟩

/-- Uniform means of the three actual present-key visit counts, in rational numbers. -/
theorem present_query_means :
    (((([3, 6, 9] : List Nat).map
      (fun q => visits (compareOfLessAndEq q) (three 3 6 9))).sum : Nat) : ℚ) / 3 = 5 / 3 ∧
    (((([3, 6, 9] : List Nat).map
      (fun q => visits (compareOfLessAndEq q) chain369)).sum : Nat) : ℚ) / 3 = 2 := by
  rw [balanced_present_visits, chain_present_visits]
  norm_num

end TreeSearchExamples
