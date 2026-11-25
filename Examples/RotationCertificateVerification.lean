import Applications.Resources.RotationCertificate.Verifier
import Examples.MeasuredRotationCertificate
import Examples.RotationCertificateCodecs

/-!
# Connected encoded rotation-certificate verification

The literal results and costs were fixed from the stage protocol before the
stream implementation. Public equations connect them to actual returned fuel,
moves, reached trees and suffixes. General clients retain arbitrary malformed
words, fixed-width high zeros, semantic soundness and small witnessed acceptance.
The measured observation remains separate from machine complexity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateVerification
open Trees Trees.Rotations Resources
open Resources.BinaryCounter (Bits value decFixedRun decFixedRun_true decFixedRun_first_true)
open Resources.RotationCertificate
open RotationDistanceExample
  (empty singleton leftTwo rightTwo leftThree balancedThree rightThree rootRight rootLeft rightAtLeft)

/-! EOF checks the actual reached shape and leaves every bit of fuel untouched. -/

theorem eof_literal_cases (bs : Bits) :
    checkStreamRun bs empty.val empty.val [] = (true, 3) ∧
      checkStreamRun bs singleton.val singleton.val [] = (true, 6) ∧
      checkStreamRun bs leftTwo.val rightTwo.val [] = (false, 5) ∧
      checkStreamRun bs empty.val singleton.val [] = (false, 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [checkStreamRun_nil] <;> rfl

theorem eof_constructor_mismatch_skips_target_subtrees
    (bs : Bits) (left right : BinaryTree Unit) :
    checkStreamRun bs .nil (.node () left right) [] = (false, 3) := by
  rw [checkStreamRun_nil, eqTreeRun_nil_node]
  rfl

theorem zero_fuel_skips_every_nonempty_raw_word
    (width : Nat) (source target : BinaryTree Unit) (tag : Tag) (tail : Word) :
    checkStreamRun (List.replicate width false) source target (tag :: tail) =
      (false, 2 * width + 4) :=
  checkStreamRun_replicate_false width source target tag tail

/-! Compose public component observations for an actual successful one-move run. -/

theorem one_move_exact (bs remaining : Bits) (source target : BinaryTree Unit)
    (move : RotationMove) (fuel : (decFixedRun bs).1 = some remaining)
    (executed : (applyMoveRun move source).1 = some target) :
    checkStreamRun bs source target (moveCode move) =
      (true, (decFixedRun bs).2 + 6 * move.position.length + 3 * source.numNodes + 13) := by
  have parsed : (parseMoveRun (moveCode move)).1 = some (move, []) := by
    simpa only [List.append_nil] using congrArg Prod.fst (parseMoveRun_code move [])
  have equal : (eqTreeRun target target).1 = true :=
    (eqTreeRun_value target target).trans (decide_eq_true rfl)
  have nodes := applyMoveRun_numNodes move source target executed
  rw [checkStreamRun_step bs remaining source target target _ [] move fuel parsed executed,
    checkStreamRun_nil]
  simp only [CallCount.tick, equal, eqTreeRun_self_cost,
    parseMoveRun_cost_of_some (moveCode move) move [] parsed,
    applyMoveRun_cost_of_some move source target executed]
  apply Prod.ext
  · rfl
  · dsimp only
    omega

theorem one_right_move :
    checkStreamRun [true] leftTwo.val rightTwo.val (certCode [rootRight]) = (true, 22) :=
  one_move_exact [true] [false] leftTwo.val rightTwo.val rootRight rfl rfl

theorem one_inverse_move :
    checkStreamRun [true] rightTwo.val leftTwo.val (certCode [rootLeft]) = (true, 22) :=
  one_move_exact [true] [false] rightTwo.val leftTwo.val rootLeft rfl rfl

theorem high_zeros_do_not_change_the_one_move_work :
    checkStreamRun [true, false, false] leftTwo.val rightTwo.val
      (certCode [rootRight]) = (true, 22) :=
  one_move_exact [true, false, false] [false, false, false]
    leftTwo.val rightTwo.val rootRight rfl rfl

theorem longer_borrow_for_a_short_witness :
    checkStreamRun [false, false, true] leftTwo.val rightTwo.val
      (certCode [rootRight]) = (true, 28) :=
  one_move_exact [false, false, true] [true, true, false]
    leftTwo.val rightTwo.val rootRight rfl rfl

theorem one_right_move_on_three_nodes :
    checkStreamRun [true] leftThree.val balancedThree.val
      (certCode [rootRight]) = (true, 25) :=
  one_move_exact [true] [false] leftThree.val balancedThree.val rootRight rfl rfl

theorem arbitrary_higher_fuel_is_unvisited_for_one_move (zeros : Nat) (higher : Bits) :
    checkStreamRun (List.replicate zeros false ++ true :: higher)
      leftTwo.val rightTwo.val (certCode [rootRight]) = (true, 3 * zeros + 22) := by
  have fuel := congrArg Prod.fst (decFixedRun_first_true zeros higher)
  have run := one_move_exact (List.replicate zeros false ++ true :: higher)
    (List.replicate zeros true ++ false :: higher)
    leftTwo.val rightTwo.val rootRight fuel rfl
  rw [decFixedRun_first_true] at run
  apply Prod.ext
  · exact congrArg Prod.fst run
  · have cost := congrArg Prod.snd run
    change (checkStreamRun (List.replicate zeros false ++ true :: higher)
      leftTwo.val rightTwo.val (certCode [rootRight])).2 =
        3 * (zeros + 1) + 0 + 6 + 13 at cost
    dsimp only
    omega

/-! A second nonempty stage must decrement before parsing, even after reaching the target. -/

theorem one_move_exhausts_before_any_second_word (width : Nat)
    (source next target : BinaryTree Unit) (move : RotationMove)
    (tag : Tag) (tail : Word) (executed : (applyMoveRun move source).1 = some next) :
    checkStreamRun (true :: List.replicate width false) source target
      (moveCode move ++ tag :: tail) =
        (false, 6 * move.position.length + 2 * width + 19) := by
  have parsed := congrArg Prod.fst (parseMoveRun_code move (tag :: tail))
  have stopped : checkStreamRun (false :: List.replicate width false) next target
      (tag :: tail) = (false, 2 * (width + 1) + 4) :=
    checkStreamRun_replicate_false (width + 1) next target tag tail
  rw [checkStreamRun_step (true :: List.replicate width false)
    (false :: List.replicate width false) source next target _ _ move rfl parsed executed]
  simp only [stopped, decFixedRun_true, parseMoveRun_code,
    applyMoveRun_cost_of_some move source next executed]
  apply Prod.ext
  · rfl
  · dsimp only
    omega

theorem high_zero_width_changes_exhaustion_work
    (target : BinaryTree Unit) (tag : Tag) (tail : Word) :
    checkStreamRun [true] leftTwo.val target (moveCode rootRight ++ tag :: tail) =
        (false, 19) ∧
      checkStreamRun [true, false, false] leftTwo.val target
        (moveCode rootRight ++ tag :: tail) = (false, 23) :=
  ⟨one_move_exhausts_before_any_second_word 0 leftTwo.val rightTwo.val target
      rootRight tag tail rfl,
    one_move_exhausts_before_any_second_word 2 leftTwo.val rightTwo.val target
      rootRight tag tail rfl⟩

theorem illegal_root_skips_the_arbitrary_suffix
    (higher : Bits) (target : BinaryTree Unit) (suffix : Word) :
    checkStreamRun (true :: higher) leftTwo.val target (moveCode rootLeft ++ suffix) =
      (false, 12) := by
  have parsed := congrArg Prod.fst (parseMoveRun_code rootLeft suffix)
  rw [checkStreamRun_move_failure (true :: higher) (false :: higher) leftTwo.val target
    _ suffix rootLeft rfl parsed rfl, parseMoveRun_code]
  rfl

theorem every_reserved_head_stops_after_fuel
    (higher : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (reserved : 11 ≤ tag.val) (tail : Word) :
    checkStreamRun (true :: higher) source target (tag :: tail) = (false, 7) := by
  have parser :=
    (Examples.RotationCertificateCodecs.every_reserved_tag_stops_before_the_tail
      tag reserved tail).2.2
  rw [checkStreamRun_parse_failure (true :: higher) (false :: higher) source target
    tag tail rfl (congrArg Prod.fst parser), parser]
  rfl

theorem missing_move_delimiters_stop_before_execution (source target : BinaryTree Unit) :
    checkStreamRun [true] source target [rotateRightTag] = (false, 9) ∧
      checkStreamRun [true] source target [rotateRightTag, pathLeftTag] = (false, 11) := by
  constructor
  · rw [checkStreamRun_parse_failure [true] [false] source target rotateRightTag [] rfl rfl]
    rfl
  · rw [checkStreamRun_parse_failure [true] [false] source target rotateRightTag
      [pathLeftTag] rfl rfl]
    rfl

theorem initial_equality_does_not_accept_early :
    checkStreamRun [true] leftTwo.val leftTwo.val (certCode [rootRight]) = (false, 18) := by
  have parsed := congrArg Prod.fst (parseMoveRun_code rootRight [])
  simp only [List.append_nil] at parsed
  simp only [certCode, List.append_nil]
  rw [checkStreamRun_step [true] [false] leftTwo.val rightTwo.val leftTwo.val
    _ [] rootRight rfl parsed rfl, checkStreamRun_nil]
  rfl

/-! Successful non-shortest routes, and positions tested against the actual current tree. -/

theorem inverse_cycle_at_threshold_two :
    checkStreamRun [false, true] leftTwo.val leftTwo.val
      (certCode [rootRight, rootLeft]) = (true, 38) := by
  have last : checkStreamRun [true, false] rightTwo.val leftTwo.val
      (moveCode rootLeft) = (true, 22) :=
    one_move_exact [true, false] [false, false] rightTwo.val leftTwo.val rootLeft rfl rfl
  have parsed := congrArg Prod.fst (parseMoveRun_code rootRight (moveCode rootLeft))
  simp only [certCode, List.append_nil]
  rw [checkStreamRun_step [false, true] [true, false] leftTwo.val rightTwo.val leftTwo.val
    _ _ rootRight rfl parsed rfl]
  simp only [last]
  rfl

theorem two_roots_use_the_reached_tree :
    checkStreamRun [false, true] leftThree.val rightThree.val
      (certCode [rootRight, rootRight]) = (true, 41) := by
  have last : checkStreamRun [true, false] balancedThree.val rightThree.val
      (moveCode rootRight) = (true, 25) :=
    one_move_exact [true, false] [false, false]
      balancedThree.val rightThree.val rootRight rfl rfl
  have parsed := congrArg Prod.fst (parseMoveRun_code rootRight (moveCode rootRight))
  simp only [certCode, List.append_nil]
  rw [checkStreamRun_step [false, true] [true, false]
    leftThree.val balancedThree.val rightThree.val _ _ rootRight rfl parsed rfl]
  simp only [last]
  rfl

theorem stale_position_stops_before_arbitrary_target_and_suffix
    (target : BinaryTree Unit) (suffix : Word) :
    checkStreamRun [false, true] leftThree.val target
      (certCode [rootRight, rightAtLeft] ++ suffix) = (false, 33) := by
  have parsedLast := congrArg Prod.fst (parseMoveRun_code rightAtLeft suffix)
  have last : checkStreamRun [true, false] balancedThree.val target
      (moveCode rightAtLeft ++ suffix) = (false, 17) := by
    rw [checkStreamRun_move_failure [true, false] [false, false] balancedThree.val target
      _ suffix rightAtLeft rfl parsedLast rfl, parseMoveRun_code]
    rfl
  have parsed :=
    congrArg Prod.fst (parseMoveRun_code rootRight (moveCode rightAtLeft ++ suffix))
  simp only [certCode, List.append_nil, List.append_assoc]
  rw [checkStreamRun_step [false, true] [true, false]
    leftThree.val balancedThree.val target _ _ rootRight rfl parsed rfl]
  simp only [last]
  rfl

theorem attained_short_witness_and_normalization_route :
    Shape.distance leftThree balancedThree = 1 ∧
      checkStreamRun [true] leftThree.val balancedThree.val
        (certCode [rootRight]) = (true, 25) ∧
      checkStreamRun [true] leftThree.val balancedThree.val
        (certCode (connectionMoves leftThree.val balancedThree.val)) = (false, 19) := by
  refine ⟨Examples.MeasuredRotationCertificate.actual_three_node_distance_one,
    one_right_move_on_three_nodes, ?_⟩
  rw [Examples.MeasuredRotationCertificate.displayed_connection_route]
  exact one_move_exhausts_before_any_second_word 0 leftThree.val balancedThree.val
    balancedThree.val rootRight rotateRightTag [endMoveTag, rotateLeftTag, endMoveTag] rfl

/-! General semantic clients use the actual stream's public recognition theorem. -/

theorem every_actual_bounded_trace_accepts (bs : Bits) (source target : BinaryTree Unit)
    (moves : List RotationMove) (run : applyMoves? moves source = some target)
    (bounded : moves.length ≤ value bs) :
    (checkStreamRun bs source target (certCode moves)).1 = true :=
  checkStreamRun_complete moves bs source target run bounded

theorem arbitrary_raw_stream_recognition
    (bs : Bits) (source target : BinaryTree Unit) (raw : Word) :
    (checkStreamRun bs source target raw).1 = true ↔
      ∃ moves, raw = certCode moves ∧ applyMoves? moves source = some target ∧
        moves.length ≤ value bs :=
  checkStreamRun_iff bs source target raw

theorem equal_numeric_fuel_has_equal_acceptance (bs cs : Bits)
    (source target : BinaryTree Unit) (raw : Word) (same : value bs = value cs) :
    (checkStreamRun bs source target raw).1 = (checkStreamRun cs source target raw).1 := by
  have equivalent : (checkStreamRun bs source target raw).1 = true ↔
      (checkStreamRun cs source target raw).1 = true := by
    rw [checkStreamRun_iff, checkStreamRun_iff, same]
  cases first : (checkStreamRun bs source target raw).1 <;>
    cases second : (checkStreamRun cs source target raw).1 <;> simp_all

theorem unequal_sizes_reject_every_certificate (bs : Bits)
    (source target : BinaryTree Unit) (raw : Word)
    (different : source.numNodes ≠ target.numNodes) :
    (checkStreamRun bs source target raw).1 = false := by
  cases result : (checkStreamRun bs source target raw).1 with
  | false => rfl
  | true =>
      obtain ⟨moves, _, run, _⟩ := checkStreamRun_sound bs source target raw result
      exact False.elim (different (applyMoves?_numNodes moves run).symm)

theorem arbitrary_stream_work (bs : Bits) (source target : BinaryTree Unit) (raw : Word) :
    (checkStreamRun bs source target raw).2 ≤
      (3 * bs.length + 3 * source.numNodes + 12) * raw.length + 3 * source.numNodes + 6 :=
  checkStreamRun_cost_le bs source target raw

/-! The complete wrapper consumes actual parsed fields and rejects input tails before streaming. -/

theorem complete_wrapper_literal_cases :
    verifyRun (inputCode empty.val empty.val []) [] = (true, 19) ∧
      verifyRun (inputCode leftTwo.val rightTwo.val [true])
        (certCode [rootRight]) = (true, 69) ∧
      verifyRun (inputCode leftTwo.val rightTwo.val [true, false, false])
        (certCode [rootRight]) = (true, 75) ∧
      verifyRun (inputCode empty.val singleton.val []) [] = (false, 26) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [verifyRun_code, (eof_literal_cases []).1]
    rfl
  · rw [verifyRun_code, one_right_move]
    rfl
  · rw [verifyRun_code, high_zeros_do_not_change_the_one_move_work]
    rfl
  · rw [verifyRun_code, (eof_literal_cases []).2.2.2]
    rfl

theorem empty_input_skips_the_entire_certificate (cert : Word) :
    verifyRun [] cert = (false, 6) := by
  rw [verifyRun_of_none [] cert rfl]
  rfl

theorem trailing_input_skips_both_arbitrary_tails (tag : Tag) (tail cert : Word) :
    verifyRun (inputCode empty.val empty.val [] ++ tag :: tail) cert = (false, 17) :=
  verifyRun_trailing_input empty.val empty.val [] tag tail cert

theorem actual_emitters_feed_an_accepting_verifier
    (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove)
    (run : applyMoves? moves source = some target) (bounded : moves.length ≤ value bs) :
    (verifyRun (emitInputRun source target bs).1
      (emitCertificateRun moves []).1).1 = true :=
  verifyRun_emit_trace source target bs moves run bounded

theorem actual_small_witness_and_its_uniform_work (input : Word) (yes : Yes input) :
    ∃ cert : Word, cert.length ≤ 2 * input.length ^ 2 ∧
      (verifyRun input cert).1 = true ∧
        (verifyRun input cert).2 ≤ 32 * (input.length + cert.length + 1) ^ 2 := by
  obtain ⟨cert, small, accepted⟩ := verifyRun_complete_small input yes
  exact ⟨cert, small, accepted, verifyRun_work_all input cert⟩

theorem malformed_words_are_still_within_the_uniform_bound (input cert : Word) :
    (verifyRun input cert).2 ≤ 32 * (input.length + cert.length + 1) ^ 2 :=
  verifyRun_work_all input cert

theorem the_one_step_language_instance_is_inhabited :
    Yes (inputCode leftTwo.val rightTwo.val [true]) := by
  apply verifyRun_sound _ (certCode [rootRight])
  exact congrArg Prod.fst complete_wrapper_literal_cases.2.1

end Examples.RotationCertificateVerification
