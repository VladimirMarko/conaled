import Applications.Trees.Rotations.Bounds
import Applications.Trees.Rotations.Existence
import Applications.Search.SharedTree.Path

/-! Independent constructor cases for the FDSA rotation contracts. -/
set_option autoImplicit false
set_option warningAsError true

namespace TreeRotationsExample
open Trees Trees.Rotations Search.SharedTree

def leaf (n : Nat) : BinaryTree Nat := .node n .nil .nil

def balancedThree : BinaryTree Nat := .node 2 (leaf 1) (leaf 3)

def rightThree : BinaryTree Nat := .node 1 .nil (.node 2 .nil (leaf 3))

def leftThree : BinaryTree Nat := .node 3 (.node 2 (leaf 1) .nil) .nil

theorem empty_right_fails : rotateRight? (.nil : BinaryTree Nat) = none := rfl

theorem empty_left_fails : rotateLeft? (.nil : BinaryTree Nat) = none := rfl

theorem leaf_right_fails : rotateRight? (leaf 7) = none := rfl

theorem leaf_left_fails : rotateLeft? (leaf 7) = none := rfl

theorem balanced_rotates : rotateRight? balancedThree = some rightThree := rfl

theorem balanced_recovers : rotateLeft? rightThree = some balancedThree := rfl

theorem left_chain_first_step : rotateRight? leftThree = some balancedThree := rfl

theorem height_changes : balancedThree.height = 2 ∧ rightThree.height = 3 := by decide

theorem shared_direction_distinct : (Branch.left == Branch.right) = false := rfl

theorem retained_search_paths :
    ([0, 1, 2, 3, 4].map (fun x => searchPathBy id x balancedThree)) =
      [[.left, .left], [.left], [], [.right], [.right, .right]] := rfl

def replaceNine (_ : BinaryTree Nat) : Option (BinaryTree Nat) := some (leaf 9)

theorem empty_position_calls_callback : applyAt? replaceNine [] .nil = some (leaf 9) := rfl

theorem terminal_empty_is_editable :
    applyAt? replaceNine [.left] (leaf 4) = some (.node 4 (leaf 9) .nil) := rfl

theorem traversal_past_empty_fails : applyAt? replaceNine [.left, .left] (leaf 4) = none := rfl

theorem longer_legal_trace :
    applyAts? rotateRight? [[.left], [], [.right]] leftThree = some rightThree := rfl

theorem longer_trace_recovers :
    applyAts? rotateLeft? [[.right], [], [.left]] rightThree = some leftThree := rfl

theorem list_form_disables_all_right_steps (p : List Branch) :
    applyAt? rotateRight? p rightThree = none :=
  no_right_rotation_of_isList (by decide) p

theorem balanced_source_algorithms :
    listOf balancedThree = rightThree ∧ rightPositions balancedThree = [[]] ∧
      countRots balancedThree = 1 := by simp [balancedThree, rightThree, leaf]

theorem left_chain_source_algorithms :
    listOf leftThree = rightThree ∧ rightPositions leftThree = [[], []] ∧
      countRots leftThree = 2 := by simp [leftThree, rightThree, leaf]

theorem longer_than_optimum :
    (rightPositions leftThree).length < ([[.left], [], [.right]] : List (List Branch)).length := by
  simp [leftThree, leaf]

theorem every_right_listification_pays_two (ps : List (List Branch)) (s : BinaryTree Nat)
    (run : applyAts? rotateRight? ps leftThree = some s) (form : IsList s) : 2 ≤ ps.length := by
  simpa only [leftThree, leaf, BinaryTree.numNodes, rightLength_node, rightLength_nil]
    using deficit_le_length run form

/- G01–G04: boundaries, exact observations and a legal nonoptimal trace. -/
theorem empty_observations :
    IsList (.nil : BinaryTree Nat) ∧ rightLength (.nil : BinaryTree Nat) = 0 ∧
      measure (.nil : BinaryTree Nat) = 0 ∧ listOf (.nil : BinaryTree Nat) = .nil ∧
      rightPositions (.nil : BinaryTree Nat) = [] ∧ countRots (.nil : BinaryTree Nat) = 0 := by
  simp [IsList, rightLength, Trees.Rotations.measure, BinaryTree.numNodes]

theorem singleton_observations :
    IsList (leaf 7) ∧ rightLength (leaf 7) = 1 ∧ measure (leaf 7) = 1 ∧
      listOf (leaf 7) = leaf 7 ∧ rightPositions (leaf 7) = [] ∧ countRots (leaf 7) = 0 := by
  simp [leaf, IsList, rightLength, Trees.Rotations.measure, BinaryTree.numNodes]

theorem three_node_observations :
    [leftThree, balancedThree, rightThree].map inorder = [[1, 2, 3], [1, 2, 3], [1, 2, 3]] ∧
      [leftThree, balancedThree, rightThree].map BinaryTree.numNodes = [3, 3, 3] ∧
      [leftThree, balancedThree, rightThree].map rightLength = [1, 2, 3] ∧
      [leftThree, balancedThree, rightThree].map measure = [5, 4, 3] := ⟨rfl, rfl, rfl, rfl⟩

def offSpine : BinaryTree Nat := .node 3 (.node 1 .nil (leaf 2)) .nil

def longerMiddle : BinaryTree Nat := .node 1 .nil (.node 3 (leaf 2) .nil)

theorem off_spine_trace_steps :
    applyAt? rotateRight? [.left] leftThree = some offSpine ∧
      rotateRight? offSpine = some longerMiddle ∧
      applyAt? rotateRight? [.right] longerMiddle = some rightThree := by
  exact ⟨rfl, rfl, rfl⟩

theorem off_spine_trace_observations :
    [leftThree, offSpine, longerMiddle, rightThree].map rightLength = [1, 1, 2, 3] ∧
      [leftThree, offSpine, longerMiddle, rightThree].map BinaryTree.numNodes = [3, 3, 3, 3] :=
  ⟨rfl, rfl⟩

/- G05–G06: later paths can become legal, and earlier ones can cease to be. -/
def balancedRight : BinaryTree Nat := .node 6 (leaf 5) (leaf 7)

def balancedSeven : BinaryTree Nat := .node 4 balancedThree balancedRight

def sevenStepOne : BinaryTree Nat := .node 2 (leaf 1) (.node 4 (leaf 3) balancedRight)

def sevenStepTwo : BinaryTree Nat :=
  .node 1 .nil (.node 2 .nil (.node 4 (leaf 3) balancedRight))

def sevenStepThree : BinaryTree Nat :=
  .node 1 .nil (.node 2 .nil (.node 3 .nil (.node 4 .nil balancedRight)))

def rightSeven : BinaryTree Nat := .node 1 .nil (.node 2 .nil (.node 3 .nil
  (.node 4 .nil (.node 5 .nil (.node 6 .nil (leaf 7))))))

theorem seven_source_algorithms :
    listOf balancedSeven = rightSeven ∧
      rightPositions balancedSeven = [[], [], [.right, .right], [.right, .right, .right, .right]] ∧
      countRots balancedSeven = 4 := by
  simp [balancedSeven, balancedThree, balancedRight, rightSeven, leaf]

theorem seven_actual_steps :
    rotateRight? balancedSeven = some sevenStepOne ∧
      rotateRight? sevenStepOne = some sevenStepTwo ∧
      applyAt? rotateRight? [.right, .right] sevenStepTwo = some sevenStepThree ∧
      applyAt? rotateRight? [.right, .right, .right, .right] sevenStepThree = some rightSeven := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem seven_observations :
    [balancedSeven, sevenStepOne, sevenStepTwo, sevenStepThree, rightSeven].map
        BinaryTree.numNodes = [7, 7, 7, 7, 7] ∧
      [balancedSeven, sevenStepOne, sevenStepTwo, sevenStepThree, rightSeven].map
        rightLength = [3, 4, 5, 6, 7] ∧
      [balancedSeven, sevenStepOne, sevenStepTwo, sevenStepThree, rightSeven].map
        measure = [11, 10, 9, 8, 7] ∧
      inorder balancedSeven = [1, 2, 3, 4, 5, 6, 7] ∧
      inorder rightSeven = [1, 2, 3, 4, 5, 6, 7] := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem seven_trace_recovers :
    applyAts? rotateLeft? [[.right, .right, .right, .right], [.right, .right], [], []]
      rightSeven = some balancedSeven := rfl

theorem initial_legality_is_not_sequential_legality :
    applyAt? rotateRight? [.left] balancedSeven = some (.node 4 rightThree balancedRight) ∧
      applyAts? rotateRight? [[], [.left]] balancedSeven = none ∧
      applyAt? rotateRight? [.right, .right] balancedSeven = none ∧
      applyAt? rotateRight? [.right, .right, .right, .right] balancedSeven = none ∧
      applyAts? rotateRight? [[], []] balancedThree = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/- G07–G08: arbitrary callbacks need not preserve contents or future legality. -/
def nestedEdit : BinaryTree Nat := .node 2 (.node 0 .nil (leaf 1)) (leaf 3)

def nestedEdited : BinaryTree Nat := .node 2 (.node 0 .nil (leaf 9)) (leaf 3)

theorem nested_callback_changes_contents :
    applyAt? replaceNine [.left, .right] nestedEdit = some nestedEdited ∧
      inorder nestedEdit = [0, 1, 2, 3] ∧ inorder nestedEdited = [0, 9, 2, 3] := by
  exact ⟨rfl, rfl, rfl⟩

def prune (_ : BinaryTree Nat) : Option (BinaryTree Nat) := some .nil

theorem pruning_success_and_failure :
    applyAts? prune [[.right]] balancedSeven = some (.node 4 balancedThree .nil) ∧
      applyAts? prune [[]] balancedRight = some .nil ∧
      applyAts? prune [[], [.right]] balancedRight = none ∧
      applyAts? prune [[.right], [.right, .right]] balancedSeven = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pruning_append_failure :
    (applyAts? prune [[.right]] balancedSeven).bind
      (applyAts? prune [[.right, .right]]) = none := rfl

theorem pruning_lift_failure :
    (applyAts? prune [[], [.right]] balancedRight).map
      (fun r => BinaryTree.node 4 balancedThree r) = none := rfl

/- G09–G10: duplicates and malformed trees are in the raw domain. -/
def duplicateLeft : BinaryTree Nat := .node 7 (leaf 7) .nil

def duplicateRight : BinaryTree Nat := .node 7 .nil (leaf 7)

def malformed : BinaryTree Nat := .node 1 (leaf 9) (leaf 0)

def malformedRight : BinaryTree Nat := .node 9 .nil (.node 1 .nil (leaf 0))

theorem duplicate_rotation_and_recovery :
    rotateRight? duplicateLeft = some duplicateRight ∧
      rotateLeft? duplicateRight = some duplicateLeft ∧
      inorder duplicateLeft = [7, 7] ∧ inorder duplicateRight = [7, 7] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem duplicate_source_algorithms :
    listOf duplicateLeft = duplicateRight ∧ rightPositions duplicateLeft = [[]] ∧
      countRots duplicateLeft = 1 := by
  simp [duplicateLeft, duplicateRight, leaf]

theorem malformed_raw_rotation :
    rotateRight? malformed = some malformedRight ∧
      inorder malformed = [9, 1, 0] ∧ inorder malformedRight = [9, 1, 0] ∧
      malformed.numNodes = malformedRight.numNodes := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem malformed_raw_set : setTree malformedRight = setTree malformed :=
  rotateRight?_setTree (show rotateRight? malformed = some malformedRight from rfl)

theorem inorder_does_not_determine_raw_shape :
    inorder balancedThree = inorder rightThree ∧ balancedThree ≠ rightThree := by
  exact ⟨rfl, by decide⟩

def pairTwelve : BinaryTree Nat := .node 1 .nil (leaf 2)

def pairTwentyOne : BinaryTree Nat := .node 2 .nil (leaf 1)

theorem same_set_different_order :
    setTree pairTwelve = setTree pairTwentyOne ∧
      pairTwelve.numNodes = pairTwentyOne.numNodes ∧ inorder pairTwelve ≠ inorder pairTwentyOne := by
  refine ⟨?_, rfl, by decide⟩
  ext x
  simp [pairTwelve, pairTwentyOne, leaf, or_comm]

theorem reversed_pair_has_no_right_trace (ps : List (List Branch)) :
    applyAts? rotateRight? ps pairTwelve ≠ some pairTwentyOne := by
  intro run
  have same := applyAts?_inorder rotateRight? rotateRight?_inorder ps run
  exact same_set_different_order.2.2 same.symm

theorem reversed_pair_has_no_left_trace (ps : List (List Branch)) :
    applyAts? rotateLeft? ps pairTwelve ≠ some pairTwentyOne := by
  intro run
  have same := applyAts?_inorder rotateLeft? rotateLeft?_inorder ps run
  exact same_set_different_order.2.2 same.symm

theorem size_does_not_determine_contents :
    (leaf 1).numNodes = (leaf 2).numNodes ∧ inorder (leaf 1) ≠ inorder (leaf 2) := by
  exact ⟨rfl, by decide⟩

theorem set_does_not_determine_multiplicity :
    setTree (leaf 7) = setTree duplicateRight ∧
      (leaf 7).numNodes ≠ duplicateRight.numNodes ∧
      inorder (leaf 7) ≠ inorder duplicateRight := by
  refine ⟨?_, by decide, by decide⟩
  ext x
  simp [leaf, duplicateRight, setTree]

/- G11: the specified two-phase connection is not a shortest mixed route. -/
def fourLeft : BinaryTree Nat := .node 4 leftThree .nil

def fourOther : BinaryTree Nat := .node 4 balancedThree .nil

theorem three_standard_connection :
    (applyAts? rotateRight? (rightPositions balancedThree) balancedThree).bind
      (applyAts? rotateLeft? (rightPositions leftThree).reverse) = some leftThree :=
  connect_equal_inorder rfl

theorem three_connection_is_not_shortest :
    (rightPositions balancedThree).length + (rightPositions leftThree).length = 3 ∧
      rotateLeft? balancedThree = some leftThree := by
  exact ⟨by simp [balancedThree, leftThree, leaf], rfl⟩

theorem four_schedules :
    rightPositions fourLeft = [[], [], []] ∧
      rightPositions fourOther = [[], [], [.right, .right]] := by
  simp [fourLeft, fourOther, leftThree, balancedThree, leaf]

theorem four_standard_connection :
    (applyAts? rotateRight? (rightPositions fourLeft) fourLeft).bind
      (applyAts? rotateLeft? (rightPositions fourOther).reverse) = some fourOther :=
  connect_equal_inorder rfl

theorem four_connection_attains_bound_but_is_not_shortest :
    (rightPositions fourLeft).length + (rightPositions fourOther).length =
        2 * fourLeft.numNodes - 2 ∧
      applyAt? rotateRight? [.left] fourLeft = some fourOther := by
  rw [four_schedules.1, four_schedules.2]
  exact ⟨rfl, rfl⟩

theorem empty_connection :
    (applyAts? rotateRight? (rightPositions (.nil : BinaryTree Nat)) (.nil : BinaryTree Nat)).bind
      (applyAts? rotateLeft? (rightPositions (.nil : BinaryTree Nat)).reverse) = some .nil ∧
      (rightPositions (.nil : BinaryTree Nat)).length * 2 = 0 := by
  simp

theorem singleton_connection :
    (applyAts? rotateRight? (rightPositions (leaf 7)) (leaf 7)).bind
      (applyAts? rotateLeft? (rightPositions (leaf 7)).reverse) = some (leaf 7) ∧
      (rightPositions (leaf 7)).length * 2 = 0 := by
  simp [leaf]

/- G12–G13: descent decreases the real measure, and chain formulas hold for every size. -/
def descentWitness : BinaryTree Nat := .node 0 .nil leftThree

theorem descent_observations :
    descentWitness.numNodes = 4 ∧ rightLength descentWitness = 2 ∧ measure descentWitness = 6 ∧
      leftThree.numNodes = 3 ∧ rightLength leftThree = 1 ∧ measure leftThree = 5 ∧
      descentWitness.numNodes - rightLength descentWitness = 2 ∧
      leftThree.numNodes - rightLength leftThree = 2 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem root_blocked_but_descendant_legal :
    rotateRight? descentWitness = none ∧
      applyAt? rotateRight? [.right] descentWitness = some (.node 0 .nil balancedThree) ∧
      ¬ IsList descentWitness := by
  exact ⟨rfl, rfl, by decide⟩

theorem descent_source_algorithms :
    rightPositions descentWitness = [[.right], [.right]] ∧ countRots descentWitness = 2 := by
  simp [descentWitness, leftThree, leaf]

theorem chain_family {α : Type _} (a : α) (n : Nat) :
    listOf (leftChain a n) = rightChain a n ∧
      rightPositions (leftChain a n) = List.replicate (n - 1) [] ∧
      countRots (leftChain a n) = n - 1 ∧
      measure (leftChain a n) = (if n = 0 then 0 else 2 * n - 1) ∧
      rightPositions (rightChain a n) = [] ∧ countRots (rightChain a n) = 0 ∧
      measure (rightChain a n) = n :=
  ⟨listOf_leftChain a n, rightPositions_leftChain a n, countRots_leftChain a n,
    measure_leftChain a n, rightPositions_rightChain a n, countRots_rightChain a n,
    measure_rightChain a n⟩

/- G14: these clients use the independent induction theorem. -/
theorem independent_empty : ∃ ps s, applyAts? rotateRight? ps (.nil : BinaryTree Nat) = some s ∧
    IsList s ∧ inorder s = [] := exists_right_list .nil

theorem independent_left_chain : ∃ ps s, applyAts? rotateRight? ps leftThree = some s ∧
    IsList s ∧ inorder s = inorder leftThree := exists_right_list leftThree

theorem independent_seven : ∃ ps s, applyAts? rotateRight? ps balancedSeven = some s ∧
    IsList s ∧ inorder s = inorder balancedSeven := exists_right_list balancedSeven

theorem longer_existential_witness : ∃ ps s,
    applyAts? rotateRight? ps leftThree = some s ∧ IsList s ∧
      inorder s = inorder leftThree ∧ ps.length = 3 :=
  ⟨[[.left], [], [.right]], rightThree, rfl, by decide, rfl, rfl⟩

/- G16–G17: existing eliminators and genuinely larger-universe labels. -/
theorem shared_direction_eliminator :
    Branch.rec (motive := fun _ => Nat) 3 4 Branch.left = 3 ∧
      Branch.rec (motive := fun _ => Nat) 3 4 Branch.right = 4 := ⟨rfl, rfl⟩

def liftedBalanced : BinaryTree (ULift.{1} Nat) :=
  .node ⟨2⟩ (.node ⟨1⟩ .nil .nil) (.node ⟨3⟩ .nil .nil)

def liftedRight : BinaryTree (ULift.{1} Nat) :=
  .node ⟨1⟩ .nil (.node ⟨2⟩ .nil (.node ⟨3⟩ .nil .nil))

theorem lifted_rotation_and_inverse :
    rotateRight? liftedBalanced = some liftedRight ∧ rotateLeft? liftedRight = some liftedBalanced :=
  ⟨rfl, rfl⟩

theorem lifted_source_algorithms :
    listOf liftedBalanced = liftedRight ∧ rightPositions liftedBalanced = [[]] ∧
      countRots liftedBalanced = 1 := by
  simp [liftedBalanced, liftedRight]

theorem lifted_observations :
    (inorder liftedBalanced).map ULift.down = [1, 2, 3] ∧
      (inorder liftedRight).map ULift.down = [1, 2, 3] ∧
      liftedBalanced.numNodes = 3 ∧ rightLength liftedBalanced = 2 ∧ measure liftedBalanced = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

#eval (rightPositions balancedThree, rightPositions leftThree,
  countRots balancedThree, countRots leftThree)

#eval (rotateRight? balancedThree == some rightThree,
  balancedThree.height, rightThree.height, rightLength balancedThree,
  rightLength rightThree, measure balancedThree)

#eval ((rightPositions balancedSeven).map (List.map (fun d => match d with
  | .left => 0 | .right => 1)), countRots balancedSeven,
  [balancedSeven, sevenStepOne, sevenStepTwo, sevenStepThree, rightSeven].map rightLength,
  [balancedSeven, sevenStepOne, sevenStepTwo, sevenStepThree, rightSeven].map measure)

#eval (applyAts? rotateRight? [[], [.left]] balancedSeven == none,
  applyAt? rotateRight? [.right, .right] balancedSeven == none,
  applyAt? rotateRight? [.right, .right] sevenStepTwo == some sevenStepThree,
  applyAts? rotateRight? [[.left], [], [.right]] leftThree == some rightThree,
  applyAts? rotateLeft? [[.right], [], [.left]] rightThree == some leftThree)

#eval (applyAt? replaceNine [] .nil == some (leaf 9),
  applyAt? replaceNine [.left, .left] (leaf 4) == none,
  (applyAt? replaceNine [.left, .right] nestedEdit).map inorder,
  applyAts? prune [[.right], [.right, .right]] balancedSeven == none)

#eval (inorder (listOf duplicateLeft), countRots duplicateLeft,
  inorder (listOf malformed), rightPositions fourLeft |>.length,
  rightPositions fourOther |>.length, countRots descentWitness)

#eval ([0, 1, 2, 3, 4, 5].map fun n =>
  (n, rightLength (leftChain 7 n), measure (leftChain 7 n), countRots (leftChain 7 n),
    rightLength (rightChain 7 n), countRots (rightChain 7 n)))

#eval ((inorder (listOf liftedBalanced)).map ULift.down, countRots liftedBalanced,
  liftedBalanced.numNodes, rightLength liftedBalanced, measure liftedBalanced)

end TreeRotationsExample
