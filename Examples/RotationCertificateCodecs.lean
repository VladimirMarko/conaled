import Applications.Resources.RotationCertificate.LinearParser
import Examples.MeasuredRotationCertificate

/-!
# Finite-word emitter and prefix-parser clients

All literal words and costs were fixed before the codec implementation.
The examples retain arbitrary suffixes and distinguish parsing syntax from
executing a rotation. Roundtrips below connect actual bit, path and move
emitters to actual prefix parsers. Tree and full-input parsing, streaming
verification and its polynomial conclusions remain separate later work.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateCodecs
open Trees Trees.Rotations Search.SharedTree Resources
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open RotationDistanceExample
  (rootRight rootLeft rightAtLeft leftAtRight empty singleton leftTwo rightTwo balancedThree)

/-! The complete fixed alphabet and independent literal preorder words. -/

theorem fixed_alphabet_codes :
    [emptyTag, nodeTag, separatorTag, bitZeroTag, bitOneTag, endInputTag,
      rotateLeftTag, rotateRightTag, pathLeftTag, pathRightTag, endMoveTag] =
        ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : Word) := rfl

theorem literal_tree_codes :
    treeCode empty.val = [emptyTag] ∧
      treeCode singleton.val = [nodeTag, emptyTag, emptyTag] ∧
      treeCode leftTwo.val = [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag] ∧
      treeCode rightTwo.val = [nodeTag, emptyTag, nodeTag, emptyTag, emptyTag] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem literal_tree_emissions (suffix : Word) :
    emitTreeRun empty.val suffix = (emptyTag :: suffix, 2) ∧
      emitTreeRun singleton.val suffix = ([nodeTag, emptyTag, emptyTag] ++ suffix, 6) ∧
      emitTreeRun leftTwo.val suffix =
        ([nodeTag, nodeTag, emptyTag, emptyTag, emptyTag] ++ suffix, 10) ∧
      emitTreeRun rightTwo.val suffix =
        ([nodeTag, emptyTag, nodeTag, emptyTag, emptyTag] ++ suffix, 10) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem literal_bit_and_path_emissions (suffix : Word) :
    emitBitsRun [] suffix = (suffix, 1) ∧
      emitBitsRun [false, false] suffix = ([bitZeroTag, bitZeroTag] ++ suffix, 5) ∧
      emitBitsRun [true, false, false] suffix =
        ([bitOneTag, bitZeroTag, bitZeroTag] ++ suffix, 7) ∧
      emitPathRun [.left, .right] suffix = ([pathLeftTag, pathRightTag] ++ suffix, 5) ∧
      emitPathRun [.right, .left] suffix = ([pathRightTag, pathLeftTag] ++ suffix, 5) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem literal_move_and_certificate_emissions (suffix : Word) :
    emitMoveRun rootRight suffix = ([rotateRightTag, endMoveTag] ++ suffix, 3) ∧
      emitMoveRun rootLeft suffix = ([rotateLeftTag, endMoveTag] ++ suffix, 3) ∧
      emitMoveRun rightAtLeft suffix =
        ([rotateRightTag, pathLeftTag, endMoveTag] ++ suffix, 5) ∧
      emitMoveRun leftAtRight suffix =
        ([rotateLeftTag, pathRightTag, endMoveTag] ++ suffix, 5) ∧
      emitCertificateRun [] suffix = (suffix, 1) ∧
      emitCertificateRun [rootRight, rootLeft] suffix =
        ([rotateRightTag, endMoveTag, rotateLeftTag, endMoveTag] ++ suffix, 9) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem literal_input_emissions :
    emitInputRun empty.val empty.val [] =
        ([emptyTag, separatorTag, emptyTag, separatorTag, endInputTag], 9) ∧
      emitInputRun leftTwo.val rightTwo.val [true] =
        ([nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, separatorTag,
          nodeTag, emptyTag, nodeTag, emptyTag, emptyTag, separatorTag,
          bitOneTag, endInputTag], 27) ∧
      (inputCode leftTwo.val rightTwo.val [true]).length = 14 := ⟨rfl, rfl, rfl⟩

/-! Arbitrary inputs consume the public emitter and length contracts. -/

theorem arbitrary_tree_emitter_contract (t : BinaryTree Unit) (suffix : Word) :
    emitTreeRun t suffix = (treeCode t ++ suffix, 4 * t.numNodes + 2) ∧
      (treeCode t).length = 2 * t.numNodes + 1 :=
  ⟨emitTreeRun_eq t suffix, treeCode_length t⟩

theorem arbitrary_linear_emitter_contracts (bs : Bits) (path : List Branch)
    (move : RotationMove) (suffix : Word) :
    emitBitsRun bs suffix = (bitTags bs ++ suffix, 2 * bs.length + 1) ∧
      emitPathRun path suffix = (pathTags path ++ suffix, 2 * path.length + 1) ∧
      emitMoveRun move suffix = (moveCode move ++ suffix, 2 * move.position.length + 3) :=
  ⟨emitBitsRun_eq bs suffix, emitPathRun_eq path suffix, emitMoveRun_eq move suffix⟩

theorem arbitrary_certificate_emitter_contract (moves : List RotationMove) (suffix : Word) :
    emitCertificateRun moves suffix =
        (certCode moves ++ suffix, 2 * (certCode moves).length + 1) ∧
      (certCode moves).length = (moves.map (fun m => m.position.length + 2)).sum :=
  ⟨emitCertificateRun_eq moves suffix, certCode_length moves⟩

theorem arbitrary_input_emitter_contract (source target : BinaryTree Unit) (bs : Bits) :
    (emitInputRun source target bs).1 = inputCode source target bs ∧
      (inputCode source target bs).length =
        2 * source.numNodes + 2 * target.numNodes + bs.length + 5 ∧
      (emitInputRun source target bs).2 + 1 = 2 * (inputCode source target bs).length ∧
      (emitInputRun source target bs).2 = 2 * (inputCode source target bs).length - 1 :=
  ⟨emitInputRun_value source target bs, inputCode_length source target bs,
    emitInputRun_cost_add_one source target bs, emitInputRun_cost source target bs⟩

/-! Prefix success returns the exact supplied suffix, even when it is foreign syntax. -/

theorem bit_parser_literal_successes (suffix : Word) :
    parseBitsRun [endInputTag] = (some ([], []), 2) ∧
      parseBitsRun ([bitZeroTag, bitZeroTag, endInputTag] ++ suffix) =
        (some ([false, false], suffix), 8) ∧
      parseBitsRun ([bitOneTag, endInputTag] ++ suffix) = (some ([true], suffix), 5) ∧
      parseBitsRun ([bitOneTag, bitZeroTag, bitZeroTag, endInputTag] ++ suffix) =
        (some ([true, false, false], suffix), 11) := ⟨rfl, rfl, rfl, rfl⟩

theorem path_parser_literal_successes (suffix : Word) :
    parsePathRun ([endMoveTag] ++ suffix) = (some ([], suffix), 2) ∧
      parsePathRun ([pathLeftTag, pathRightTag, endMoveTag] ++ suffix) =
        (some ([.left, .right], suffix), 8) ∧
      parsePathRun ([pathRightTag, pathLeftTag, endMoveTag] ++ suffix) =
        (some ([.right, .left], suffix), 8) := ⟨rfl, rfl, rfl⟩

theorem move_parser_literal_successes (suffix : Word) :
    parseMoveRun ([rotateRightTag, endMoveTag] ++ suffix) = (some (rootRight, suffix), 4) ∧
      parseMoveRun ([rotateLeftTag, endMoveTag] ++ suffix) = (some (rootLeft, suffix), 4) ∧
      parseMoveRun ([rotateRightTag, pathLeftTag, endMoveTag] ++ suffix) =
        (some (rightAtLeft, suffix), 7) ∧
      parseMoveRun ([rotateLeftTag, pathRightTag, endMoveTag] ++ suffix) =
        (some (leftAtRight, suffix), 7) := ⟨rfl, rfl, rfl, rfl⟩

theorem missing_delimiters_fail_at_the_reached_end :
    parseBitsRun [] = (none, 2) ∧
      parseBitsRun [bitZeroTag, bitZeroTag] = (none, 6) ∧
      parsePathRun [pathLeftTag] = (none, 4) ∧
      parsePathRun [pathLeftTag, pathRightTag] = (none, 6) ∧
      parseMoveRun [rotateRightTag] = (none, 4) ∧
      parseMoveRun [rotateRightTag, pathLeftTag] = (none, 6) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem foreign_tag_stops_before_arbitrary_tail (tail : Word) :
    parseBitsRun (separatorTag :: tail) = (none, 2) ∧
      parsePathRun (endInputTag :: tail) = (none, 2) ∧
      parseMoveRun (endMoveTag :: tail) = (none, 2) ∧
      parseMoveRun ((15 : Tag) :: tail) = (none, 2) := ⟨rfl, rfl, rfl, rfl⟩

theorem reached_foreign_tags_stop_reconstruction (tail : Word) :
    parseBitsRun (bitZeroTag :: separatorTag :: tail) = (none, 4) ∧
      parsePathRun (pathRightTag :: endInputTag :: tail) = (none, 4) ∧
      parseMoveRun (rotateLeftTag :: bitZeroTag :: tail) = (none, 4) := ⟨rfl, rfl, rfl⟩

theorem reserved_tag_is_not_syntax_for_any_prefix (tail : Word) :
    parseBitsRun ((15 : Tag) :: tail) = (none, 2) ∧
      parsePathRun ((15 : Tag) :: tail) = (none, 2) ∧
      parseMoveRun ((15 : Tag) :: tail) = (none, 2) := ⟨rfl, rfl, rfl⟩

theorem every_reserved_tag_stops_before_the_tail (tag : Tag) (reserved : 11 ≤ tag.val)
    (tail : Word) :
    parseBitsRun (tag :: tail) = (none, 2) ∧
      parsePathRun (tag :: tail) = (none, 2) ∧
      parseMoveRun (tag :: tail) = (none, 2) := by
  have different (allowed : Tag) (small : allowed.val < 11) : tag ≠ allowed := by
    intro same
    subst tag
    omega
  exact ⟨parseBitsRun_foreign tag tail (different _ (by decide))
      (different _ (by decide)) (different _ (by decide)),
    parsePathRun_foreign tag tail (different _ (by decide))
      (different _ (by decide)) (different _ (by decide)),
    parseMoveRun_foreign tag tail (different _ (by decide)) (different _ (by decide))⟩

/-! These iff statements describe all raw inputs, not only successful encoder outputs. -/

theorem bit_prefix_iff (raw : Word) (bs : Bits) (rest : Word) :
    (parseBitsRun raw).1 = some (bs, rest) ↔
      raw = bitTags bs ++ [endInputTag] ++ rest := parseBitsRun_iff raw bs rest

theorem path_prefix_iff (raw : Word) (path : List Branch) (rest : Word) :
    (parsePathRun raw).1 = some (path, rest) ↔
      raw = pathTags path ++ [endMoveTag] ++ rest := parsePathRun_iff raw path rest

theorem move_prefix_iff (raw : Word) (move : RotationMove) (rest : Word) :
    (parseMoveRun raw).1 = some (move, rest) ↔ raw = moveCode move ++ rest :=
  parseMoveRun_iff raw move rest

theorem arbitrary_prefix_parser_work (raw : Word) :
    (parseBitsRun raw).2 ≤ 3 * raw.length + 2 ∧
      (parsePathRun raw).2 ≤ 3 * raw.length + 2 ∧
      (parseMoveRun raw).2 ≤ 4 * raw.length + 2 :=
  ⟨parseBitsRun_cost_le raw, parsePathRun_cost_le raw, parseMoveRun_cost_le raw⟩

theorem actual_successful_bit_consumption (raw : Word) (bs : Bits) (rest : Word)
    (returned : (parseBitsRun raw).1 = some (bs, rest)) :
    raw.length = bs.length + 1 + rest.length ∧ (parseBitsRun raw).2 = 3 * bs.length + 2 :=
  ⟨parseBitsRun_consumed_length raw bs rest returned,
    parseBitsRun_cost_of_some raw bs rest returned⟩

theorem actual_successful_path_consumption (raw : Word) (path : List Branch) (rest : Word)
    (returned : (parsePathRun raw).1 = some (path, rest)) :
    raw.length = path.length + 1 + rest.length ∧
      (parsePathRun raw).2 = 3 * path.length + 2 :=
  ⟨parsePathRun_consumed_length raw path rest returned,
    parsePathRun_cost_of_some raw path rest returned⟩

theorem actual_successful_move_consumption (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) :
    raw.length = move.position.length + 2 + rest.length ∧
      rest.length < raw.length ∧ (parseMoveRun raw).2 = 3 * move.position.length + 4 :=
  ⟨parseMoveRun_consumed_length raw move rest returned,
    parseMoveRun_rest_length_lt raw move rest returned,
    parseMoveRun_cost_of_some raw move rest returned⟩

/-! Actual emitter outputs are fed directly to their actual prefix parsers. -/

theorem actual_bit_emitter_parser_roundtrip (bs : Bits) (rest : Word) :
    parseBitsRun (emitBitsRun bs (endInputTag :: rest)).1 =
      (some (bs, rest), 3 * bs.length + 2) := parseBitsRun_emit bs rest

theorem actual_path_emitter_parser_roundtrip (path : List Branch) (rest : Word) :
    parsePathRun (emitPathRun path (endMoveTag :: rest)).1 =
      (some (path, rest), 3 * path.length + 2) := parsePathRun_emit path rest

theorem actual_move_emitter_parser_roundtrip (move : RotationMove) (rest : Word) :
    parseMoveRun (emitMoveRun move rest).1 =
      (some (move, rest), 3 * move.position.length + 4) := parseMoveRun_emit move rest

theorem bit_prefix_uniquely_determines_both_results (first second : Bits)
    (rest suffix : Word)
    (same : bitTags first ++ [endInputTag] ++ rest =
      bitTags second ++ [endInputTag] ++ suffix) : first = second ∧ rest = suffix :=
  parseBitsRun_prefix_injective first second rest suffix same

theorem path_prefix_uniquely_determines_both_results (first second : List Branch)
    (rest suffix : Word)
    (same : pathTags first ++ [endMoveTag] ++ rest =
      pathTags second ++ [endMoveTag] ++ suffix) : first = second ∧ rest = suffix :=
  parsePathRun_prefix_injective first second rest suffix same

theorem move_prefix_uniquely_determines_both_results (first second : RotationMove)
    (rest suffix : Word) (same : moveCode first ++ rest = moveCode second ++ suffix) :
    first = second ∧ rest = suffix :=
  parseMoveRun_prefix_injective first second rest suffix same

theorem high_zero_width_survives_the_actual_roundtrip (width : Nat) (rest : Word) :
    parseBitsRun (emitBitsRun (true :: List.replicate width false) (endInputTag :: rest)).1 =
      (some (true :: List.replicate width false, rest), 3 * (width + 1) + 2) := by
  simpa only [List.length_cons, List.length_replicate] using
    actual_bit_emitter_parser_roundtrip (true :: List.replicate width false) rest

theorem zero_width_survives_the_actual_roundtrip (width : Nat) (rest : Word) :
    parseBitsRun (emitBitsRun (List.replicate width false) (endInputTag :: rest)).1 =
      (some (List.replicate width false, rest), 3 * width + 2) := by
  simpa only [List.length_replicate] using
    actual_bit_emitter_parser_roundtrip (List.replicate width false) rest

theorem parsing_does_not_assert_rotation_legality (rest : Word) :
    parseMoveRun (emitMoveRun rootRight rest).1 = (some (rootRight, rest), 4) ∧
      applyMoveRun rootRight empty.val = (none, 3) ∧
      parseMoveRun (emitMoveRun rightAtLeft rest).1 = (some (rightAtLeft, rest), 7) ∧
      applyMoveRun rightAtLeft balancedThree.val = (none, 5) :=
  ⟨actual_move_emitter_parser_roundtrip rootRight rest, rfl,
    actual_move_emitter_parser_roundtrip rightAtLeft rest,
    Examples.MeasuredRotationCertificate.measured_stale_position_separator.2.2.1⟩

end Examples.RotationCertificateCodecs
