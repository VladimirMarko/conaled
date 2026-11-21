import Applications.Resources.BinaryCounter.FixedWidth
import Applications.Resources.BinaryCounter.Decrement
import Applications.Resources.RotationCertificate.Execution
import Examples.RotationDistance

/-!
# Connected fixed-width and structural rotation work

These clients retain the literal expectations fixed before implementation.
The observation counts actual source dispatch, reconstruction and returned
constructors. Width is distinct from decoded magnitude, and a reached missing
tree or left equality failure leaves its unvisited suffix untouched. The
normalization route is compared with the existing attained minimum, without
claiming a parser, streaming verifier or machine-time result.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredRotationCertificate
open Trees Trees.Rotations Search.SharedTree Resources
open Resources.BinaryCounter
open Resources.RotationCertificate
open RotationDistanceExample
  (rootRight rootLeft rightAtLeft leftAtRight empty singleton leftTwo rightTwo
    leftThree balancedThree rightThree offSpineThree)
universe u

/-! Exact fixed-width observations, including redundant high zero bits. -/

theorem fixed_width_literal_cases :
    decFixedRun [] = (none, 2) ∧
      decFixedRun [true] = (some [false], 3) ∧
      decFixedRun [false, true] = (some [true, false], 6) ∧
      decFixedRun [false, false, true] = (some [true, true, false], 9) ∧
      decFixedRun [true, false, false] = (some [false, false, false], 3) ∧
      decFixedRun [false, false, false] = (none, 8) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem canonical_predecessor_has_a_different_width_contract :
    decBits [true] = some [] ∧ decFixedRun [true] = (some [false], 3) := ⟨rfl, rfl⟩

theorem first_true_retains_arbitrary_suffix (r : Nat) (tail : Bits) :
    decFixedRun (List.replicate r false ++ true :: tail) =
      (some (List.replicate r true ++ false :: tail), 3 * (r + 1)) :=
  decFixedRun_first_true r tail

theorem zero_width_controls_failure_cost (width : Nat) :
    decFixedRun (List.replicate width false) = (none, 2 * width + 2) :=
  decFixedRun_replicate_false width

theorem successful_predecessor_width_and_value (bs ys : Bits)
    (returned : (decFixedRun bs).1 = some ys) :
    ys.length = bs.length ∧ value bs = value ys + 1 :=
  decFixedRun_some_spec returned

theorem predecessor_exists_exactly_when_positive (bs : Bits) :
    ((decFixedRun bs).1 = none ↔ value bs = 0) ∧
      ((∃ ys, (decFixedRun bs).1 = some ys) ↔ 0 < value bs) ∧
      (decFixedRun bs).2 ≤ 3 * bs.length + 2 :=
  ⟨decFixedRun_none_iff bs, decFixedRun_exists_iff bs, decFixedRun_cost_le bs⟩

theorem positive_predecessor_has_the_original_width (bs : Bits)
    (positive : 0 < value bs) :
    ∃ ys, (decFixedRun bs).1 = some ys ∧ ys.length = bs.length ∧
      value bs = value ys + 1 := by
  obtain ⟨ys, returned⟩ := decFixedRun_exists_of_pos positive
  exact ⟨ys, returned, decFixedRun_some_spec returned⟩

/-- Numeric magnitude may vary through the reused suffix; this actual cost does not. -/
theorem true_head_cost_is_independent_of_the_suffix (first second : Bits) :
    decFixedRun (true :: first) = (some (false :: first), 3) ∧
      decFixedRun (true :: second) = (some (false :: second), 3) :=
  ⟨decFixedRun_true first, decFixedRun_true second⟩

/-! Partial root and positioned execution on the existing concrete shapes. -/

theorem root_rotation_cases :
    rotateRun .right leftTwo.val = (some rightTwo.val, 4) ∧
      rotateRun .left leftTwo.val = (none, 2) ∧
      applyMoveRun rootRight leftTwo.val = (some rightTwo.val, 5) ∧
      applyMoveRun rootLeft leftTwo.val = (none, 3) ∧
      applyMoveRun rightAtLeft balancedThree.val = (none, 5) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem inverse_root_rotation_case :
    rotateRun .left rightTwo.val = (some leftTwo.val, 4) ∧
      applyMoveRun rootLeft rightTwo.val = (some leftTwo.val, 5) := ⟨rfl, rfl⟩

theorem arbitrary_missing_path_stops {α : Type u}
    (direction : RotationDirection) (branch : Branch) (tail : List Branch) :
    applyMoveRun ⟨direction, branch :: tail⟩ (.nil : BinaryTree α) = (none, 2) := rfl

/-- One reached ancestor costs two extra units; no remaining branch is inspected. -/
theorem missing_below_singleton_stops (direction : RotationDirection)
    (branch : Branch) (tail : List Branch) :
    applyMoveRun ⟨direction, .left :: branch :: tail⟩ singleton.val = (none, 4) ∧
      applyMoveRun ⟨direction, .right :: branch :: tail⟩ singleton.val = (none, 4) :=
  ⟨rfl, rfl⟩

/-- An empty position invokes its callback even at nil, and retains its new result. -/
theorem empty_position_callback_at_nil {α : Type u} (a : α) :
    applyAtRun (fun _ : BinaryTree α => (some (.node a .nil .nil), 7)) [] .nil =
      (some (.node a .nil .nil), 8) := rfl

theorem empty_position_callback_failure_at_nil {α : Type u} :
    applyAtRun (fun _ : BinaryTree α => (none, 7)) [] .nil = (none, 8) := rfl

/-- Both branches reconstruct with the callback's actual replacement and other child. -/
theorem actual_replacement_is_reconstructed {α : Type u} (a : α)
    (left right replacement : BinaryTree α) :
    applyAtRun (fun _ : BinaryTree α => (some replacement, 7)) [.left]
        (.node a left right) = (some (.node a replacement right), 11) ∧
      applyAtRun (fun _ : BinaryTree α => (some replacement, 7)) [.right]
        (.node a left right) = (some (.node a left replacement), 11) := ⟨rfl, rfl⟩

theorem arbitrary_label_rotation {α : Type u} (a b : α) (A B C : BinaryTree α) :
    rotateRun .right (.node b (.node a A B) C) =
        (some (.node a A (.node b B C)), 4) ∧
      rotateRun .left (.node a A (.node b B C)) =
        (some (.node b (.node a A B) C), 4) := ⟨rfl, rfl⟩

theorem actual_rotations_erase {α : Type u} (direction : RotationDirection)
    (move : RotationMove) (t : BinaryTree α) :
    (rotateRun direction t).1 = direction.apply? t ∧
      (applyMoveRun move t).1 = applyMove? move t :=
  ⟨rotateRun_value direction t, applyMoveRun_value move t⟩

theorem actual_callback_erasure {α : Type u}
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat)
    (f : BinaryTree α → Option (BinaryTree α)) (position : List Branch)
    (t : BinaryTree α) (values : ∀ input, (fRun input).1 = f input) :
    (applyAtRun fRun position t).1 = applyAt? f position t :=
  applyAtRun_value fRun f position t values

theorem successful_move_depth_size_and_cost {α : Type u}
    (move : RotationMove) (source target : BinaryTree α)
    (returned : (applyMoveRun move source).1 = some target) :
    move.position.length + 2 ≤ source.numNodes ∧
      target.numNodes = source.numNodes ∧
      (applyMoveRun move source).2 = 3 * move.position.length + 5 :=
  ⟨applyMoveRun_depth_le move source target returned,
    applyMoveRun_numNodes move source target returned,
    applyMoveRun_cost_of_some move source target returned⟩

theorem arbitrary_move_work {α : Type u} (move : RotationMove) (source : BinaryTree α) :
    (applyMoveRun move source).2 ≤ 3 * source.numNodes + 3 :=
  applyMoveRun_cost_le move source

theorem actual_success_has_the_existing_partial_inverse {α : Type u}
    (move : RotationMove) (source target : BinaryTree α)
    (returned : (applyMoveRun move source).1 = some target) :
    (applyMoveRun move.opposite target).1 = some source :=
  applyMoveRun_undo move source target returned

/-! Equality is structural, left-first and independent of the target's unmatched size. -/

theorem structural_equality_literal_cases :
    eqTreeRun empty.val empty.val = (true, 2) ∧
      eqTreeRun singleton.val singleton.val = (true, 5) ∧
      eqTreeRun leftTwo.val leftTwo.val = (true, 8) ∧
      eqTreeRun leftTwo.val rightTwo.val = (false, 4) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem left_mismatch_skips_arbitrary_right_trees
    (sourceRight targetRight : BinaryTree Unit) :
    eqTreeRun (.node () singleton.val sourceRight)
      (.node () .nil targetRight) = (false, 4) :=
  eqTreeRun_of_left_false singleton.val sourceRight .nil targetRight rfl

theorem constructor_mismatch_skips_arbitrary_target
    (left right : BinaryTree Unit) :
    eqTreeRun .nil (.node () left right) = (false, 2) := rfl

theorem structural_equality_public_contract (source target : BinaryTree Unit) :
    (eqTreeRun source target).1 = decide (source = target) ∧
      (eqTreeRun source target).2 ≤ 3 * source.numNodes + 2 ∧
      (eqTreeRun source source).2 = 3 * source.numNodes + 2 :=
  ⟨eqTreeRun_value source target, eqTreeRun_cost_le source target,
    eqTreeRun_self_cost source⟩

/-! State-dependent positions and the actual attained minimum remain separate. -/

theorem measured_stale_position_separator :
    applyMoveRun rootRight leftThree.val = (some balancedThree.val, 5) ∧
      applyMoveRun rightAtLeft leftThree.val = (some offSpineThree.val, 8) ∧
      applyMoveRun rightAtLeft balancedThree.val = (none, 5) ∧
      applyMoves? [rootRight, rightAtLeft] leftThree.val = none :=
  ⟨rfl, rfl, rfl, RotationDistanceExample.stale_position_fails⟩

theorem displayed_normalization_positions :
    rightPositions leftThree.val = [[], []] ∧
      rightPositions balancedThree.val = [[]] := by
  constructor
  · exact rightPositions_leftChain () 3
  · change rightPositions (.node () (.node () .nil .nil) (.node () .nil .nil)) = [[]]
    simp

theorem displayed_connection_route :
    connectionMoves leftThree.val balancedThree.val = [rootRight, rootRight, rootLeft] := by
  simp [connectionMoves, displayed_normalization_positions.1,
    displayed_normalization_positions.2, directedMoves, rootRight, rootLeft]

theorem displayed_connection_length_and_result :
    (connectionMoves leftThree.val balancedThree.val).length = 3 ∧
      applyMoves? (connectionMoves leftThree.val balancedThree.val) leftThree.val =
        some balancedThree.val := by
  refine ⟨?_, apply_connectionMoves (Shape.inorder_eq leftThree balancedThree)⟩
  rw [displayed_connection_route]
  rfl

theorem actual_three_node_distance_one : Shape.distance leftThree balancedThree = 1 := by
  have upper := Shape.distance_le_length leftThree balancedThree
    RotationDistanceExample.initially_legal_moves.1
  have positive : Shape.distance leftThree balancedThree ≠ 0 := by
    intro zero
    have different : leftThree ≠ balancedThree := by decide
    exact different ((Shape.distance_eq_zero_iff leftThree balancedThree).mp zero)
  change Shape.distance leftThree balancedThree ≤ 1 at upper
  omega

theorem attained_minimum_is_shorter_than_the_connection_route :
    ∃ moves : List RotationMove,
      applyMoves? moves leftThree.val = some balancedThree.val ∧
        moves.length = 1 ∧ moves.length < (connectionMoves leftThree.val balancedThree.val).length := by
  obtain ⟨moves, executed, length⟩ := Shape.distance_spec leftThree balancedThree
  have one : moves.length = 1 := length.trans actual_three_node_distance_one
  refine ⟨moves, executed, one, ?_⟩
  rw [one, displayed_connection_length_and_result.1]
  decide

end Examples.MeasuredRotationCertificate
