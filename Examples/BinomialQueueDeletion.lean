import Applications.Search.BinomialQueue.Contract

/-!
Independent constructor expectations for every deletion phase, occurrence
preservation through both interfaces, and ties in a non-antisymmetric order.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BinomialQueueDeletion

open Search.BinomialQueue

/-- The right sibling 8 need not be below its left sibling 3. -/
def rankTwo : BinaryTree Nat :=
  .node 10 (.node 3 (.node 1 .nil .nil) (.node 8 .nil .nil)) .nil

def childrenTwo : Queue Nat :=
  [.node 8 .nil .nil, .node 3 (.node 1 .nil .nil) .nil]

theorem rankTwo_valid : pow2heap 2 rankTwo := by simp [rankTwo, pow2heap, pow2heapAux]

theorem rankTwo_not_binary_heap_order : ¬ (8 ≤ (3 : Nat)) := by decide

theorem rankTwo_unzip : heapDeleteMax rankTwo = childrenTwo := rfl

theorem rankTwo_children_ranks : priq childrenTwo ∧ childrenTwo.length = 2 :=
  ⟨heapDeleteMax_valid rankTwo_valid, heapDeleteMax_length rankTwo_valid⟩

theorem rankTwo_children_mass : mass childrenTwo = 3 :=
  heapDeleteMax_mass rankTwo_valid

theorem rankTwo_children_bound : ∀ x ∈ contents childrenTwo, x ≤ 10 :=
  heapDeleteMax_bound rankTwo_valid

theorem rankTwo_occurrences : contents childrenTwo = [8, 3, 1] := rfl

theorem unzip_nonidentity :
    unzip (.node 3 (.node 1 .nil .nil) (.node 8 .nil .nil))
      (fun q => .node 42 .nil .nil :: q) =
      [.node 8 .nil .nil, .node 3 (.node 1 .nil .nil) .nil, .node 42 .nil .nil] := rfl

theorem unzip_continuation_suffix (cont : Queue Nat → Queue Nat) :
    unzip (.node 3 (.node 1 .nil .nil) (.node 8 .nil .nil)) cont =
      childrenTwo ++ cont [] :=
  unzip_eq_append _ cont

theorem unzip_continuation_not_wrapper :
    unzip (.node 3 (.node 1 .nil .nil) (.node 8 .nil .nil))
      (fun q => .node 42 .nil .nil :: q) ≠ .node 42 .nil .nil :: childrenTwo := by decide

def firstForest : Queue Nat :=
  [.node 9 .nil .nil, .node 5 (.node 1 .nil .nil) .nil]

def firstRest : Queue Nat := [.nil, .node 5 (.node 1 .nil .nil) .nil]

theorem firstForest_valid : priq firstForest := by
  simp [priq, firstForest, priqFrom, pow2heap, pow2heapAux]

theorem first_auxiliary : deleteMaxAux natGreater 9 firstForest = (firstRest, []) := rfl

theorem first_delete : deleteMax natGreater firstForest = some (9, firstRest) := rfl

def middleForest : Queue Nat :=
  [.nil, .node 9 (.node 2 .nil .nil) .nil,
    .node 7 (.node 3 (.node 1 .nil .nil) (.node 6 .nil .nil)) .nil]

def middleRest : Queue Nat :=
  [.node 2 .nil .nil, .nil,
    .node 7 (.node 3 (.node 1 .nil .nil) (.node 6 .nil .nil)) .nil]

theorem middleForest_valid : priq middleForest := by
  simp [priq, middleForest, priqFrom, pow2heap, pow2heapAux]

theorem middle_auxiliary : deleteMaxAux natGreater 9 middleForest =
    ([.nil, .nil, .node 7 (.node 3 (.node 1 .nil .nil) (.node 6 .nil .nil)) .nil],
      [.node 2 .nil .nil]) := rfl

theorem middle_delete : deleteMax natGreater middleForest = some (9, middleRest) := rfl

def lastForest : Queue Nat := [.node 0 .nil .nil, .nil, rankTwo]

def lastRest : Queue Nat :=
  [.nil, .nil, .node 8 (.node 3 (.node 1 .nil .nil) (.node 0 .nil .nil)) .nil]

theorem lastForest_valid : priq lastForest := by
  simp [priq, lastForest, rankTwo, priqFrom, pow2heap, pow2heapAux]

theorem last_auxiliary : deleteMaxAux natGreater 10 lastForest =
    ([.node 0 .nil .nil, .nil, .nil], childrenTwo) := rfl

theorem last_delete : deleteMax natGreater lastForest = some (10, lastRest) := rfl

theorem last_full_contract :
    priq lastRest ∧ (contents lastForest).Perm (10 :: contents lastRest) ∧
      ∀ x ∈ contents lastRest, x ≤ 10 :=
  ⟨deleteMax_some_priq natGreater_eq lastForest lastRest 10 lastForest_valid last_delete,
    deleteMax_some_relate natGreater_eq lastForest lastRest 10 _ _ lastForest_valid
      (queue_elems_contents _) last_delete (queue_elems_contents _)⟩

theorem last_exact_loss : mass lastRest + 1 = mass lastForest :=
  deleteMax_some_mass natGreater_eq _ _ _ lastForest_valid last_delete

theorem last_stored_length : lastRest.length = lastForest.length :=
  deleteMax_length natGreater_eq _ _ _ lastForest_valid last_delete

def rankThree : BinaryTree Nat := smash natGreater rankTwo rankTwo

theorem rankThree_valid : pow2heap 3 rankThree :=
  smash_valid natGreater natGreater_eq 2 _ _ rankTwo_valid rankTwo_valid

theorem shifted_valid : priqFrom 2 [.nil, rankThree] :=
  ⟨Or.inl rfl, Or.inr rankThree_valid, trivial⟩

theorem shifted_find : findMax natGreater [.nil, rankThree] = some 10 := rfl

theorem shifted_auxiliary : deleteMaxAux natGreater 10 [.nil, rankThree] =
    ([.nil, .nil], heapDeleteMax rankThree) := rfl

theorem shifted_child_base_zero :
    priq (deleteMaxAux natGreater 10 [.nil, rankThree]).2 ∧
      (deleteMaxAux natGreater 10 [.nil, rankThree]).2.length = 3 :=
  ⟨(deleteMaxAux_valid natGreater_eq 2 _ _ shifted_valid shifted_find).2,
    heapDeleteMax_length rankThree_valid⟩

theorem shifted_first_base_two :
    priqFrom 2 (deleteMaxAux natGreater 10 [.nil, rankThree]).1 :=
  (deleteMaxAux_valid natGreater_eq 2 _ _ shifted_valid shifted_find).1

theorem empty_delete : deleteMax natGreater [] = none := rfl

theorem padded_empty_delete (n : Nat) :
    deleteMax natGreater (List.replicate n .nil) = none :=
  (deleteMax_eq_none_iff natGreater _).mpr (by simp)

theorem padded_empty_abs (n : Nat) : Abs (List.replicate n (.nil : BinaryTree Nat)) [] :=
  (abs_nil_iff _).mpr (by simp)

theorem singleton_zero_delete :
    deleteMax natGreater [.node 0 .nil .nil] = some (0, [.nil]) := rfl

theorem singleton_residual_is_not_empty : ([.nil] : Queue Nat) ≠ [] := by decide

def repeated : Queue Nat := [.node 7 .nil .nil, .node 7 (.node 1 .nil .nil) .nil]
def repeatedOnce : Queue Nat := [.nil, .node 7 (.node 1 .nil .nil) .nil]
def repeatedTwice : Queue Nat := [.node 1 .nil .nil, .nil]

theorem repeated_valid : priq repeated := by
  simp [priq, repeated, priqFrom, pow2heap, pow2heapAux]

theorem repeated_first : deleteMax natGreater repeated = some (7, repeatedOnce) := rfl

theorem repeated_second : deleteMax natGreater repeatedOnce = some (7, repeatedTwice) := rfl

theorem repeated_counts : (contents repeated).count 7 = 2 ∧
    (contents repeatedOnce).count 7 = 1 ∧ (contents repeatedTwice).count 7 = 0 := by decide

theorem repeated_source_contract :
    [7, 1, 7].Perm (7 :: [1, 7]) ∧ ∀ x ∈ [1, 7], x ≤ (7 : Nat) :=
  natLaws.deleteMax_relate repeated repeatedOnce 7 [7, 1, 7] [1, 7] repeated_valid
    ((queue_elems_iff _ _).mpr (by decide)) repeated_first
    ((queue_elems_iff _ _).mpr (by decide))

def repeatedQueue : {q : Queue Nat // priq q} := ⟨repeated, repeated_valid⟩
def repeatedOnceQueue : {q : Queue Nat // priq q} := ⟨repeatedOnce, by
  simp [priq, repeatedOnce, priqFrom, pow2heap, pow2heapAux]⟩

theorem repeated_exact_remove :
    exactQueue.remove repeatedQueue = some (Search.MaximumQueue.encode 7, repeatedOnceQueue) :=
  (exactQueue_remove_some _ _ _).mpr repeated_first

theorem repeated_exact_entries :
    exactQueue.entries repeatedQueue =
      [Search.MaximumQueue.encode 7, Search.MaximumQueue.encode 7, Search.MaximumQueue.encode 1] := rfl

def singletonSeven : {q : Queue Nat // priq q} := ⟨[.node 7 .nil .nil], by
  simp [priq, priqFrom, pow2heap, pow2heapAux]⟩

theorem native_meld_shape :
    (mergeValid singletonSeven singletonSeven).val =
      [.nil, .node 7 (.node 7 .nil .nil) .nil] := rfl

theorem native_meld_entries :
    (exactQueue.entries (mergeValid singletonSeven singletonSeven)).Perm
      [Search.MaximumQueue.encode 7, Search.MaximumQueue.encode 7] :=
  mergeValid_entries singletonSeven singletonSeven

def malformed : BinaryTree Nat := .node 9 .nil (.node 0 .nil .nil)

theorem malformed_not_heap (n : Nat) : ¬ pow2heap n malformed := by simp [pow2heap, malformed]

theorem malformed_heap_fallback : heapDeleteMax malformed = [] := rfl

theorem malformed_auxiliary_prefix :
    deleteMaxAux natGreater 9 [.nil, .node 1 .nil .nil, malformed] =
      ([.nil, .node 1 .nil .nil], []) := rfl

theorem malformed_delete_fallback : deleteMax natGreater [malformed] = some (9, []) := rfl

theorem malformed_occurrence_loss : ¬ (contents [malformed]).Perm [9] := by decide

section Tagged

/-- Distinct tags at equal priorities are equivalent in this preorder. -/
local instance taggedPreorder : Preorder (Nat × Bool) where
  le x y := x.1 ≤ y.1
  lt x y := x.1 ≤ y.1 ∧ ¬ y.1 ≤ x.1
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl x := Nat.le_refl x.1
  le_trans _ _ _ hxy hyz := Nat.le_trans hxy hyz

local instance taggedLE : LE (Nat × Bool) := taggedPreorder.toLE

local instance taggedTotal : Std.Total (fun x y : Nat × Bool => x ≤ y) where
  total x y := Nat.le_total x.1 y.1

def taggedGreater (x y : Nat × Bool) : Bool := decide (y.1 < x.1)

theorem taggedGreater_law (x y : Nat × Bool) : taggedGreater x y = true ↔ ¬ x ≤ y := by
  change decide (y.1 < x.1) = true ↔ ¬ x.1 ≤ y.1
  simp

def taggedForest : Queue (Nat × Bool) :=
  [.node (7, false) .nil .nil, .node (7, true) (.node (1, false) .nil .nil) .nil]

def taggedRest : Queue (Nat × Bool) :=
  [.nil, .node (7, true) (.node (1, false) .nil .nil) .nil]

theorem tagged_distinct_equivalent : (7, false) ≠ (7, true) ∧
    (7, false) ≤ (7, true) ∧ ((7, true) : Nat × Bool) ≤ (7, false) :=
  ⟨by decide, Nat.le_refl 7, Nat.le_refl 7⟩

theorem taggedForest_valid : priq taggedForest := by
  refine ⟨Or.inr trivial, Or.inr ?_, trivial⟩
  exact ⟨show (1 : Nat) ≤ 7 by decide, trivial, trivial⟩

theorem tagged_first_scan : findMax taggedGreater taggedForest = some (7, false) := rfl

theorem tagged_first_delete :
    deleteMax taggedGreater taggedForest = some ((7, false), taggedRest) := rfl

theorem tagged_other_maximum_retained : (7, true) ∈ contents taggedRest := by decide

theorem tagged_deletion_contract : priq taggedRest ∧
    (contents taggedForest).Perm ((7, false) :: contents taggedRest) ∧
      ∀ x ∈ contents taggedRest, x ≤ (7, false) :=
  ⟨deleteMax_some_priq taggedGreater_law _ _ _ taggedForest_valid tagged_first_delete,
    deleteMax_some_relate taggedGreater_law _ _ _ _ _ taggedForest_valid
      (queue_elems_contents _) tagged_first_delete (queue_elems_contents _)⟩

end Tagged

end Examples.BinomialQueueDeletion
