import Applications.Search.BinomialQueue.Ranked

/-!
Source-shape and occurrence clients of dense binomial queues. The full source
left fold is checked as a tree equality, then connected to general validity and
occurrence laws. Small branch examples distinguish tie choices and dense holes.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BinomialQueues

open Search.BinomialQueue

universe u

def singleton (k : Nat) : BinaryTree Nat := .node k .nil .nil

theorem singleton_rank (k : Nat) : pow2heap 0 (singleton k) := trivial

theorem singleton_mass (k : Nat) : (singleton k).numNodes = 1 :=
  pow2heap_numNodes (singleton_rank k)

theorem singleton_height (k : Nat) : (singleton k).height = 1 :=
  pow2heap_height (singleton_rank k)

/-- This is the source command's left fold, not the adapter's right-fold batch. -/
def build (xs : List Nat) (q : Queue Nat := empty) : Queue Nat :=
  xs.foldl (fun q k => insert natGreater k q) q

theorem build_valid (xs : List Nat) (q : Queue Nat) (hq : priq q) : priq (build xs q) := by
  induction xs generalizing q with
  | nil => exact hq
  | cons k xs ih => exact ih _ (insert_priq natGreater natGreater_eq k q hq)

theorem build_relate (xs : List Nat) (q : Queue Nat) (al : List Nat)
    (hq : priq q) (hal : Abs q al) : Abs (build xs q) (xs.reverse ++ al) := by
  induction xs generalizing q al with
  | nil => exact hal
  | cons k xs ih =>
    have h := ih (insert natGreater k q) (k :: al)
      (insert_priq natGreater natGreater_eq k q hq) (insert_relate natGreater q al k hq hal)
    simpa [build, List.reverse_cons, List.append_assoc] using h

def sourceInput : List Nat := [3, 1, 4, 1, 5, 9, 2, 3, 5]

def sourceRankThree : BinaryTree Nat :=
  .node 9
    (.node 4 (.node 3 (singleton 1) (singleton 1))
      (.node 3 (singleton 2) (singleton 5))) .nil

def sourceForest : Queue Nat := [singleton 5, .nil, .nil, sourceRankThree]

/-- The independent forest displayed by VFA, including the duplicate/tie shape. -/
theorem source_fold_shape : build sourceInput empty = sourceForest := by decide

theorem source_fold_valid : priq sourceForest := by
  rw [← source_fold_shape]
  exact build_valid sourceInput empty empty_priq

theorem source_fold_occurrences : Abs sourceForest sourceInput := by
  have h := build_relate sourceInput empty [] empty_priq empty_relate
  rw [source_fold_shape] at h
  exact priqueue_elems_ext sourceForest sourceInput.reverse sourceInput
    (by decide) (by simpa using h)

theorem source_fold_mass : mass sourceForest = 9 :=
  (abs_length sourceForest sourceInput source_fold_occurrences).symm

theorem source_fold_maximum : findMax natGreater sourceForest = some 9 := by decide

theorem source_fold_rank_three : pow2heap 3 sourceRankThree :=
  source_fold_valid.2.2.2.1.resolve_left (by simp [sourceRankThree])

theorem source_rank_three_size : sourceRankThree.numNodes = 8 :=
  pow2heap_numNodes source_fold_rank_three

theorem source_rank_three_height : sourceRankThree.height = 4 :=
  pow2heap_height source_fold_rank_three

/-- The sibling 8 is allowed to exceed its left sibling 3 under outer root 10. -/
def siblingExample : BinaryTree Nat :=
  .node 10 (.node 3 (singleton 1) (singleton 8)) .nil

theorem sibling_example_rank : pow2heap 2 siblingExample := by
  simp [siblingExample, singleton, pow2heap, pow2heapAux]

theorem sibling_example_size : siblingExample.numNodes = 4 :=
  pow2heap_numNodes sibling_example_rank

theorem sibling_example_bound : ∀ x ∈ treeContents siblingExample, x ≤ 10 :=
  pow2heap_bound sibling_example_rank

def tiedLeft : BinaryTree Nat := .node 5 (singleton 1) .nil
def tiedRight : BinaryTree Nat := .node 5 (singleton 2) .nil

theorem tied_left_rank : pow2heap 1 tiedLeft := by
  simp [tiedLeft, singleton, pow2heap, pow2heapAux]

theorem tied_right_rank : pow2heap 1 tiedRight := by
  simp [tiedRight, singleton, pow2heap, pow2heapAux]

theorem tied_smash_shape : smash natGreater tiedLeft tiedRight =
    .node 5 (.node 5 (singleton 1) (singleton 2)) .nil := by decide

theorem tied_smash_rank : pow2heap 2 (smash natGreater tiedLeft tiedRight) :=
  smash_valid natGreater natGreater_eq 1 tiedLeft tiedRight tied_left_rank tied_right_rank

theorem tied_smash_occurrences : TreeElems (smash natGreater tiedLeft tiedRight) [5, 1, 5, 2] :=
  smash_elems natGreater 1 tiedLeft tiedRight [5, 1] [5, 2] tied_left_rank tied_right_rank
    (tree_elems_contents _) (tree_elems_contents _)

theorem tied_smash_permuted_witness :
    TreeElems (smash natGreater tiedLeft tiedRight) [2, 5, 1, 5] :=
  tree_elems_ext _ _ _ (by decide) tied_smash_occurrences

theorem tied_smash_two_maxima :
    (treeContents (smash natGreater tiedLeft tiedRight)).count 5 = 2 := by
  have h := Sequences.Multiplicity.perm_contents
    ((tree_elems_iff _ _).mp tied_smash_occurrences)
  exact (congrFun h 5).symm

def slot : Option Nat → BinaryTree Nat
  | none => .nil
  | some k => singleton k

theorem slot_rank (key : Option Nat) : slot key = .nil ∨ pow2heap 0 (slot key) := by
  cases key with
  | none => exact Or.inl rfl
  | some k => exact Or.inr (singleton_rank k)

/-- All eight occupancy choices use the same general rank-preservation theorem. -/
theorem one_slot_join_valid (a b c : Option Nat) :
    priq (join natGreater [slot a] [slot b] (slot c)) :=
  join_valid natGreater natGreater_eq 0 _ _ _ ⟨slot_rank a, trivial⟩
    ⟨slot_rank b, trivial⟩ (slot_rank c)

theorem join_000 : join natGreater [.nil] [.nil] .nil = [.nil] := by decide
theorem join_001 : join natGreater [.nil] [.nil] (singleton 3) = [singleton 3] := by decide
theorem join_010 : join natGreater [.nil] [singleton 2] .nil = [singleton 2] := by decide
theorem join_011 : join natGreater [.nil] [singleton 2] (singleton 3) =
    [.nil, .node 3 (singleton 2) .nil] := by decide
theorem join_100 : join natGreater [singleton 1] [.nil] .nil = [singleton 1] := by decide
theorem join_101 : join natGreater [singleton 1] [.nil] (singleton 3) =
    [.nil, .node 3 (singleton 1) .nil] := by decide
theorem join_110 : join natGreater [singleton 1] [singleton 2] .nil =
    [.nil, .node 2 (singleton 1) .nil] := by decide
theorem join_111 : join natGreater [singleton 1] [singleton 2] (singleton 3) =
    [singleton 3, .node 2 (singleton 1) .nil] := by decide

theorem join_three_occurrences :
    Abs (join natGreater [singleton 1] [singleton 2] (singleton 3)) [3, 1, 2] :=
  join_elems natGreater 0 _ _ _ [1] [2] [3] ⟨Or.inr (singleton_rank 1), trivial⟩
    ⟨Or.inr (singleton_rank 2), trivial⟩ (Or.inr (singleton_rank 3))
    (queue_elems_contents _) (queue_elems_contents _) (tree_elems_contents _)

theorem join_empty_left (q : Queue Nat) (c : BinaryTree Nat) :
    join natGreater [] q c = carry natGreater q c := join_nil_left _ _ _

theorem join_empty_right (p : Queue Nat) (c : BinaryTree Nat) :
    join natGreater p [] c = carry natGreater p c := join_nil_right _ _ _

theorem carry_empty_leaf : carry natGreater [] .nil = ([] : Queue Nat) := carry_nil_nil _

theorem carry_empty_singleton (k : Nat) : carry natGreater [] (singleton k) = [singleton k] :=
  carry_nil_node _ _ _ _

theorem carry_first_hole (q : Queue Nat) (k : Nat) :
    carry natGreater (.nil :: q) (singleton k) = singleton k :: q := carry_hole _ _ _

theorem carry_leaf_retains (q : Queue Nat) : carry natGreater q .nil = q := carry_leaf _ _

def lowThree : Queue Nat := build [1, 2, 3, 4, 5, 6, 7] empty

theorem low_three_valid : priq lowThree := build_valid _ _ empty_priq

theorem low_three_occupancy : occupancy lowThree = [true, true, true] := by decide

theorem carry_three_places (k : Nat) :
    occupancy (insert natGreater k lowThree) = [false, false, false, true] := by
  rw [occupancy_insert natGreater k lowThree low_three_valid, low_three_occupancy]
  rfl

/-- A non-lawful comparator still preserves occurrences on proper outer shapes. -/
theorem arbitrary_comparator_contents {K : Type u} (greater : K → K → Bool)
    (a b : K) : (treeContents (smash greater (.node a .nil .nil) (.node b .nil .nil))).Perm [a, b] :=
  smash_contents_nodes greater a b .nil .nil

def malformed : BinaryTree Nat := .node 9 .nil (singleton 8)

theorem malformed_smash : smash natGreater malformed (singleton 1) = .nil :=
  smash_bad_left natGreater 9 8 .nil .nil .nil (singleton 1)

theorem malformed_not_proper : ¬ Proper malformed := by simp [malformed, singleton]

theorem malformed_smash_loses_occurrences :
    ¬ (treeContents (smash natGreater malformed (singleton 1))).Perm [9, 8, 1] := by
  rw [malformed_smash]
  decide

theorem malformed_heap_delete : heapDeleteMax malformed = [] :=
  heapDeleteMax_bad 9 8 .nil .nil .nil

theorem malformed_aux : deleteMaxAux natGreater 9 [malformed] = ([], []) :=
  deleteMaxAux_bad natGreater 9 9 8 .nil .nil .nil []

theorem padded_valid (n : Nat) : priq (List.replicate n (.nil : BinaryTree Nat)) :=
  replicate_nil_valid 0 n

theorem padded_mass (n : Nat) : mass (List.replicate n (.nil : BinaryTree Nat)) = 0 :=
  replicate_nil_mass n

theorem padded_find_none (n : Nat) :
    findMax natGreater (List.replicate n (.nil : BinaryTree Nat)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem singleton_zero_some : deleteMax natGreater [singleton 0] = some (0, [.nil]) := by decide

theorem singleton_delete_not_canonical :
    deleteMax natGreater [singleton 7] = some (7, [.nil]) ∧
      ¬ Canonical ([.nil] : Queue Nat) := by
  constructor
  · decide
  · simp

theorem insertion_occupancy (k : Nat) :
    occupancy (insert natGreater k sourceForest) =
      Resources.BinaryCounter.inc (occupancy sourceForest) :=
  occupancy_insert natGreater k sourceForest source_fold_valid

theorem source_mass_digits : mass sourceForest =
    Resources.BinaryCounter.value (occupancy sourceForest) := by
  simpa using mass_eq_value source_fold_valid

theorem source_canonical : Canonical sourceForest :=
  (canonical_iff _).mpr (Or.inr ⟨[singleton 5, .nil, .nil], sourceRankThree, rfl,
    by simp [sourceRankThree]⟩)

theorem source_slot_length : sourceForest.length = (mass sourceForest).size :=
  canonical_length source_fold_valid source_canonical

theorem source_insert_length (k : Nat) : (insert natGreater k sourceForest).length = 4 := by
  rw [insert_length natGreater natGreater_eq k sourceForest source_fold_valid, source_fold_mass]
  decide

theorem source_merge_length : (merge natGreater sourceForest sourceForest).length = 5 := by
  rw [merge_length natGreater natGreater_eq sourceForest sourceForest source_fold_valid
    source_fold_valid, source_fold_mass]
  decide

theorem padded_insert_retains_length (n : Nat) (hn : 0 < n) (k : Nat) :
    (insert natGreater k (List.replicate n (.nil : BinaryTree Nat))).length = n := by
  rw [insert_length natGreater natGreater_eq k _ (padded_valid n), padded_mass]
  simp only [List.length_replicate, Nat.zero_add, Nat.size_one]
  omega

theorem padded_not_canonical (n : Nat) (hn : 0 < n) :
    ¬ Canonical (List.replicate n (.nil : BinaryTree Nat)) := by
  intro hc
  have h := canonical_length (padded_valid n) hc
  rw [padded_mass] at h
  simp only [List.length_replicate, Nat.size_zero] at h
  omega

/-- Stored slots are not bounded by live mass on the actual valid carrier. -/
theorem zero_mass_arbitrary_padding (bound : Nat) :
    ∃ q : Queue Nat, priq q ∧ mass q = 0 ∧ bound < q.length :=
  ⟨List.replicate (bound + 1) .nil, padded_valid _, padded_mass _, by simp⟩

end Examples.BinomialQueues
