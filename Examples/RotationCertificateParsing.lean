import Applications.Resources.RotationCertificate.InputParser
import Examples.RotationCertificateCodecs

/-!
# Connected tree and complete-input parser cases

The literal words, costs and failure boundaries were fixed in the retained
certificate preparation before parser implementation. These clients also use
the public recognition, work, uniqueness and actual-emitter roundtrip results
on arbitrary inputs. Complete input parsing establishes syntax; it does not
establish equal endpoint sizes, rotation legality or distance-threshold truth.
All costs below are the declared structural source-event observation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateParsing
open Trees Trees.Rotations Resources
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open RotationDistanceExample (empty singleton leftTwo rightTwo)

/-! Literal preorder cases use the public arbitrary-suffix consumption theorem. -/

theorem literal_tree_prefixes (suffix : Word) :
    parseTreeRun (emptyTag :: suffix) = (some (empty.val, suffix), 3) ∧
      parseTreeRun ([nodeTag, emptyTag, emptyTag] ++ suffix) =
        (some (singleton.val, suffix), 10) ∧
      parseTreeRun ([nodeTag, nodeTag, emptyTag, emptyTag, emptyTag] ++ suffix) =
        (some (leftTwo.val, suffix), 17) ∧
      parseTreeRun ([nodeTag, emptyTag, nodeTag, emptyTag, emptyTag] ++ suffix) =
        (some (rightTwo.val, suffix), 17) :=
  ⟨parseTreeRun_code empty.val suffix, parseTreeRun_code singleton.val suffix,
    parseTreeRun_code leftTwo.val suffix, parseTreeRun_code rightTwo.val suffix⟩

theorem missing_tree_children_fail :
    parseTreeRun [] = (none, 2) ∧
      parseTreeRun [nodeTag] = (none, 4) ∧
      parseTreeRun [nodeTag, emptyTag] = (none, 7) := ⟨rfl, rfl, rfl⟩

theorem foreign_suffix_is_untouched (tail : Word) :
    parseTreeRun (emptyTag :: rotateRightTag :: tail) =
      (some (empty.val, rotateRightTag :: tail), 3) :=
  parseTreeRun_code empty.val (rotateRightTag :: tail)

theorem foreign_tree_tag_stops_before_arbitrary_tail (tail : Word) :
    parseTreeRun (rotateRightTag :: tail) = (none, 2) ∧
      parseTreeRun (separatorTag :: tail) = (none, 2) := by
  exact ⟨parseTreeLoop_foreign rotateRightTag tail [] (by decide) (by decide),
    parseTreeLoop_foreign separatorTag tail [] (by decide) (by decide)⟩

/-- This covers each reserved symbol 11, 12, 13, 14 and 15. -/
theorem every_reserved_tag_rejects_at_tree_start (tag : Tag) (reserved : 11 ≤ tag.val)
    (tail : Word) : parseTreeRun (tag :: tail) = (none, 2) := by
  have different (allowed : Tag) (small : allowed.val < 11) : tag ≠ allowed := by
    intro same
    subst tag
    omega
  exact parseTreeLoop_foreign tag tail [] (different _ (by decide))
    (different _ (by decide))

theorem arbitrary_tree_recognition (raw : Word) (tree : BinaryTree Unit) (suffix : Word) :
    (parseTreeRun raw).1 = some (tree, suffix) ↔ raw = treeCode tree ++ suffix :=
  parseTreeRun_iff raw tree suffix

theorem actual_tree_success_retains_consumption_and_work
    (raw : Word) (tree : BinaryTree Unit) (suffix : Word)
    (returned : (parseTreeRun raw).1 = some (tree, suffix)) :
    raw.length = 2 * tree.numNodes + 1 + suffix.length ∧
      suffix.length < raw.length ∧ (parseTreeRun raw).2 = 7 * tree.numNodes + 3 :=
  ⟨parseTreeRun_consumed_length raw tree suffix returned,
    parseTreeRun_rest_length_lt raw tree suffix returned,
    parseTreeRun_cost_of_some raw tree suffix returned⟩

theorem tree_prefix_uniquely_determines_both_results (source target : BinaryTree Unit)
    (rest suffix : Word) (same : treeCode source ++ rest = treeCode target ++ suffix) :
    source = target ∧ rest = suffix :=
  treeCode_prefix_injective source target rest suffix same

theorem actual_tree_emitter_parser_roundtrip (tree : BinaryTree Unit) (suffix : Word) :
    parseTreeRun (emitTreeRun tree suffix).1 =
      (some (tree, suffix), 7 * tree.numNodes + 3) := parseTreeRun_emit tree suffix

/-- Decoding and then actually emitting the returned prefix/suffix restores the raw word. -/
theorem actual_tree_parser_emitter_restores_raw
    (raw : Word) (tree : BinaryTree Unit) (suffix : Word)
    (returned : (parseTreeRun raw).1 = some (tree, suffix)) :
    (emitTreeRun tree suffix).1 = raw := by
  rw [emitTreeRun_value]
  exact ((parseTreeRun_iff raw tree suffix).mp returned).symm

theorem actual_tree_roundtrip_combined_work (tree : BinaryTree Unit) (suffix : Word) :
    (emitTreeRun tree suffix).2 + (parseTreeRun (emitTreeRun tree suffix).1).2 =
      11 * tree.numNodes + 5 := by
  rw [emitTreeRun_cost, parseTreeRun_emit]
  dsimp
  omega

/-! Complete input parser calibrations and failure cases. -/

theorem literal_complete_inputs :
    parseInputRun [emptyTag, separatorTag, emptyTag, separatorTag, endInputTag] =
      (some (empty.val, empty.val, []), 15) ∧
      parseInputRun [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, separatorTag,
        nodeTag, emptyTag, nodeTag, emptyTag, emptyTag, separatorTag,
        bitOneTag, endInputTag] = (some (leftTwo.val, rightTwo.val, [true]), 46) :=
  ⟨parseInputRun_code empty.val empty.val [],
    parseInputRun_code leftTwo.val rightTwo.val [true]⟩

theorem missing_input_parts_reject :
    (parseInputRun []).1 = none ∧
      (parseInputRun [emptyTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag, emptyTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag, emptyTag, separatorTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag, emptyTag, separatorTag, bitZeroTag]).1 =
        none := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wrong_and_repeated_input_delimiters_reject :
    (parseInputRun [emptyTag, emptyTag, separatorTag, endInputTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag, emptyTag, endInputTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag, separatorTag, emptyTag,
        separatorTag, endInputTag]).1 = none ∧
      (parseInputRun [emptyTag, separatorTag, emptyTag, separatorTag,
        endMoveTag]).1 = none := ⟨rfl, rfl, rfl, rfl⟩

theorem missing_input_tree_children_reject :
    (parseInputRun [nodeTag, separatorTag, emptyTag, separatorTag, endInputTag]).1 =
        none ∧
      (parseInputRun [emptyTag, separatorTag, nodeTag, emptyTag,
        separatorTag, endInputTag]).1 = none := ⟨rfl, rfl⟩

theorem every_reserved_tag_rejects_at_input_start (tag : Tag)
    (reserved : 11 ≤ tag.val) (tail : Word) :
    parseInputRun (tag :: tail) = (none, 4) := by
  rw [parseInputRun, every_reserved_tag_rejects_at_tree_start tag reserved tail]
  rfl

theorem every_reserved_threshold_tag_stops_before_arbitrary_tail (tag : Tag)
    (reserved : 11 ≤ tag.val) (tail : Word) :
    parseInputRun (emptyTag :: separatorTag :: emptyTag :: separatorTag :: tag :: tail) =
      (none, 14) := by
  have different (allowed : Tag) (small : allowed.val < 11) : tag ≠ allowed := by
    intro same
    subst tag
    omega
  have bits := parseBitsRun_foreign tag tail (different _ (by decide))
    (different _ (by decide)) (different _ (by decide))
  change parseInputRun (treeCode empty.val ++ separatorTag ::
    (treeCode empty.val ++ separatorTag :: tag :: tail)) = (none, 14)
  simp only [parseInputRun, parseTreeRun_code, parseSeparatorRun_separator,
    bits, CallCount.tick, Resources.bind]
  rfl

theorem trailing_material_rejects_without_traversing_it
    (source target : BinaryTree Unit) (bs : Bits) (tag : Tag) (tail : Word) :
    parseInputRun (inputCode source target bs ++ tag :: tail) =
      (none, 7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15) :=
  parseInputRun_trailing source target bs tag tail

theorem literal_input_trailing_tag_rejects (tag : Tag) (tail : Word) :
    parseInputRun (emptyTag :: separatorTag :: emptyTag :: separatorTag ::
      endInputTag :: tag :: tail) = (none, 15) :=
  parseInputRun_trailing empty.val empty.val [] tag tail

theorem redundant_high_zeros_are_preserved :
    parseInputRun [emptyTag, separatorTag, emptyTag, separatorTag,
      bitOneTag, bitZeroTag, bitZeroTag, endInputTag] =
        (some (empty.val, empty.val, [true, false, false]), 24) ∧
      parseInputRun [emptyTag, separatorTag, emptyTag, separatorTag,
        bitZeroTag, bitZeroTag, endInputTag] =
          (some (empty.val, empty.val, [false, false]), 21) :=
  ⟨parseInputRun_code empty.val empty.val [true, false, false],
    parseInputRun_code empty.val empty.val [false, false]⟩

theorem equal_numeric_thresholds_do_not_identify_input_words :
    BinaryCounter.value ([] : Bits) = BinaryCounter.value [false, false] ∧
      inputCode empty.val empty.val [] ≠ inputCode empty.val empty.val [false, false] :=
  ⟨rfl, by decide⟩

/-- The syntax parser accepts unequal sizes, though no mixed rotation trace connects them. -/
theorem parsing_does_not_assert_equal_size_or_reachability :
    parseInputRun (inputCode empty.val singleton.val []) =
      (some (empty.val, singleton.val, []), 22) ∧
      ∀ moves : List RotationMove, applyMoves? moves empty.val ≠ some singleton.val := by
  refine ⟨parseInputRun_code empty.val singleton.val [], ?_⟩
  intro moves run
  have sizes := applyMoves?_numNodes moves run
  change 1 = 0 at sizes
  omega

/-! Arbitrary-input clients consume every new public contract. -/

theorem arbitrary_complete_input_recognition (raw : Word) (source target : BinaryTree Unit)
    (bs : Bits) :
    (parseInputRun raw).1 = some (source, target, bs) ↔ raw = inputCode source target bs :=
  parseInputRun_iff raw source target bs

theorem arbitrary_raw_parser_work (raw : Word) :
    (parseTreeRun raw).2 ≤ 5 * raw.length + 2 ∧
      (parseInputRun raw).2 ≤ 20 * (raw.length + 1) :=
  ⟨parseTreeRun_cost_le raw, parseInputRun_cost_le raw⟩

theorem actual_input_emitter_parser_roundtrip (source target : BinaryTree Unit) (bs : Bits) :
    parseInputRun (emitInputRun source target bs).1 =
      (some (source, target, bs),
        7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15) :=
  parseInputRun_emit source target bs

theorem input_code_uniquely_determines_all_fields
    (source target source' target' : BinaryTree Unit) (bs bs' : Bits)
    (same : inputCode source target bs = inputCode source' target' bs') :
    source = source' ∧ target = target' ∧ bs = bs' :=
  inputCode_injective source target bs source' target' bs' same

theorem actual_input_parser_emitter_restores_raw (raw : Word)
    (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    (emitInputRun source target bs).1 = raw := by
  rw [emitInputRun_value]
  exact ((parseInputRun_iff raw source target bs).mp returned).symm

/-- These bounds use the actual successful parse, not a separate runtime size pass. -/
theorem successful_input_bounds_each_encoded_component (raw : Word)
    (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    raw.length = 2 * source.numNodes + 2 * target.numNodes + bs.length + 5 ∧
      source.numNodes ≤ raw.length ∧ target.numNodes ≤ raw.length ∧
      bs.length ≤ raw.length ∧
      (parseInputRun raw).2 =
        7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15 := by
  have sizes := parseInputRun_sizes_le raw source target bs returned
  exact ⟨parseInputRun_length raw source target bs returned,
    sizes.1, sizes.2.1, sizes.2.2,
    parseInputRun_cost_of_some raw source target bs returned⟩

theorem arbitrary_high_zero_width_survives_full_roundtrip
    (source target : BinaryTree Unit) (width : Nat) :
    parseInputRun (emitInputRun source target (true :: List.replicate width false)).1 =
      (some (source, target, true :: List.replicate width false),
        7 * source.numNodes + 7 * target.numNodes + 3 * (width + 1) + 15) := by
  simpa only [List.length_cons, List.length_replicate] using
    parseInputRun_emit source target (true :: List.replicate width false)

end Examples.RotationCertificateParsing
