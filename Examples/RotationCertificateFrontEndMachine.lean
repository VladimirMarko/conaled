import Applications.Resources.RotationCertificate.FrontEndMachine
import Examples.RotationCertificateBinary

/-!
# Connected executions of the framed binary front end

The expected words, stage clocks, literal resets and caller boundaries were fixed
before this client and the composed implementation. The examples consume the
actual installed program and complete configurations. They distinguish syntactic
handoff from rotation legality, measured source work from machine transitions,
and the first live return from any subsequent caller instruction.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateFrontEndMachine
open Trees Resources
open Resources.BinaryCounter (Bits value)
open Resources.RotationCertificate
open FrontEndMachine
open BitPairFraming (frame escapeBits)
open RotationDistanceExample (empty singleton leftTwo rightTwo rootRight)

def SmallAlphabet : Bool → Type
  | false => Bool
  | true => Tag

instance smallAlphabetFintype (slot : Bool) : Fintype (SmallAlphabet slot) := by
  cases slot with
  | false => change Fintype Bool; infer_instance
  | true => change Fintype Tag; infer_instance

def smallContext (bits : Bits) (word : Word) : ∀ slot, List (SmallAlphabet slot)
  | false => bits
  | true => word

def sampleContext : ∀ slot, List (SmallAlphabet slot) :=
  smallContext [false, true, false] [15, 6, 1]

def staleDecoder : OpenDecoderMachine.Temporaries :=
  ⟨some true, some false, some true, some false, some 12⟩

def staleRegisters (callerBit : Bool) : Registers Bool :=
  ((some 15, some ()), staleDecoder, callerBit)

def haltCaller : External Unit → Statement SmallAlphabet Unit Bool := fun _ => .halt

theorem the_concrete_physical_types_have_the_fixed_finite_sizes :
    Fintype.card (StackId Bool) = 16 ∧
      Fintype.card (Label Unit) = 39 ∧
      Fintype.card (Registers Bool) = 93636 ∧
      Fintype.card {label : Label Unit // Owned (some label)} = 36 := by
  refine ⟨?_, ?_, ?_, owned_card⟩
  · rw [stackId_card]
    decide
  · rw [label_card]
    decide
  · rw [registers_card]
    decide

/-- Each component has a complete injective control map, including its caller complement. -/
theorem actual_component_label_maps_do_not_collapse_calls :
    Function.Injective (framerLabelEquiv (Λ := Unit)) ∧
      Function.Injective (inputDecoderLabelEquiv (Λ := Unit)) ∧
      Function.Injective (inputLabelEquiv (Λ := Unit)) ∧
      Function.Injective (certificateDecoderLabelEquiv (Λ := Unit)) ∧
      inputDecoderLabel (Λ := Unit) .scan ≠ certificateDecoderLabel .scan :=
  ⟨framerLabelEquiv.injective, inputDecoderLabelEquiv.injective,
    inputLabelEquiv.injective, certificateDecoderLabelEquiv.injective, by intro same; cases same⟩

/-- The first three returns are actual next-stage labels and remain globally owned. -/
theorem the_three_internal_handoffs_are_owned :
    framerLabelEquiv (OpenFramingMachine.resultLabel .success) =
        inputDecoderLabel (Λ := Unit) .scan ∧
      inputDecoderLabelEquiv (OpenDecoderMachine.resultLabel .success) =
        InputParserMachine.treeLabel (Λ := ExtraLabel Unit) .source .init ∧
      inputLabelEquiv (InputParserMachine.resultLabel .success) =
        certificateDecoderLabel (Λ := Unit) .scan ∧
      Owned (some (inputDecoderLabel (Λ := Unit) .scan)) ∧
      Owned (some (InputParserMachine.treeLabel (Λ := ExtraLabel Unit) .source .init)) ∧
      Owned (some (certificateDecoderLabel (Λ := Unit) .scan)) ∧
      ¬ Owned (some (dispatchLabel (Λ := Unit))) ∧
      ¬ Owned (some (rejectLabel (Λ := Unit))) := by
  refine ⟨framerLabelEquiv_success, inputDecoderLabelEquiv_success,
    input_success_is_certificate_scan, owned_inputDecoder .scan, ?_,
    owned_certificateDecoder .scan, not_owned_dispatch, not_owned_reject⟩
  exact input_fullOwned_owned _ True.intro

section Generic
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

/-- The first actual endpoint contains two direct Bool stacks, with no result markers. -/
theorem framing_returns_the_actual_two_fields (input cert : Bits) :
    Trace caller (entry regs (frame input cert) ctx)
      (inputDecoderEntry regs input cert ctx) (2 * input.length + 2 * cert.length + 4) := by
  simpa only [BitPairFraming.unframe_frame, BitPairFraming.runSteps_frame, framerResult] using
    framer_trace caller regs (frame input cert) ctx

theorem the_input_decoder_returns_the_actual_word (word : Word) (cert : Bits) :
    Trace caller (inputDecoderEntry regs (wordBits word) cert ctx)
      (inputEntry regs word cert ctx) (2 * word.length + 2) := by
  simpa only [unpackWordRun_code, OpenDecoderMachine.runSteps_code, inputDecoderResult] using
    inputDecoder_trace caller regs (wordBits word) cert ctx

theorem the_input_parser_returns_actual_fields (source target : BinaryTree Unit)
    (fuel cert : Bits) :
    Trace caller (inputEntry regs (inputCode source target fuel) cert ctx)
      (certificateDecoderEntry regs source target fuel cert ctx)
      (2 * (inputCode source target fuel).length + 3) := by
  have count := InputParserMachine.inputSteps_of_some (inputCode source target fuel)
    source target fuel (congrArg Prod.fst (parseInputRun_code source target fuel))
  simpa only [parseInputRun_code, inputResult, count] using
    input_trace caller regs (inputCode source target fuel) cert ctx

theorem the_certificate_decoder_returns_a_word_not_a_move_proof
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    Trace caller (certificateDecoderEntry regs source target fuel (wordBits cert) ctx)
      (cfg (some dispatchLabel) (reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target,
          fuel := fuel, certificateWord := cert } ctx) (2 * cert.length + 2) := by
  simpa only [unpackWordRun_code, OpenDecoderMachine.runSteps_code,
    certificateDecoderResult, resultCfg, successData] using
    certificateDecoder_trace caller regs source target fuel (wordBits cert) ctx

/-- All four executions share one program and the literal state at each boundary. -/
theorem encoded_fields_have_all_four_actual_handoffs
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    (next caller)^[8 * (inputCode source target fuel).length + 8 * cert.length + 4]
        (some (entry regs (frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) =
      some (inputDecoderEntry regs (wordBits (inputCode source target fuel)) (wordBits cert) ctx) ∧
    (next caller)^[10 * (inputCode source target fuel).length + 8 * cert.length + 6]
        (some (entry regs (frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) =
      some (inputEntry regs (inputCode source target fuel) (wordBits cert) ctx) ∧
    (next caller)^[12 * (inputCode source target fuel).length + 8 * cert.length + 9]
        (some (entry regs (frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) =
      some (certificateDecoderEntry regs source target fuel (wordBits cert) ctx) ∧
    (next caller)^[12 * (inputCode source target fuel).length + 10 * cert.length + 11]
        (some (entry regs (frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target,
          fuel := fuel, certificateWord := cert } ctx) := by
  have first := framing_returns_the_actual_two_fields caller regs ctx
    (wordBits (inputCode source target fuel)) (wordBits cert)
  have second := the_input_decoder_returns_the_actual_word caller regs ctx
    (inputCode source target fuel) (wordBits cert)
  have third := the_input_parser_returns_actual_fields caller regs ctx source target fuel (wordBits cert)
  have fourth := the_certificate_decoder_returns_a_word_not_a_move_proof
    caller regs ctx source target fuel cert
  have a := first.run
  have b := (Trace.trans caller first second).run
  have c := (Trace.trans caller (Trace.trans caller first second) third).run
  have d := (Trace.trans caller (Trace.trans caller (Trace.trans caller first second) third) fourth).run
  simp only [wordBits_length] at a b c d
  rw [show 2 * (4 * (inputCode source target fuel).length) + 2 * (4 * cert.length) + 4 =
    8 * (inputCode source target fuel).length + 8 * cert.length + 4 by omega] at a
  rw [show (2 * (4 * (inputCode source target fuel).length) + 2 * (4 * cert.length) + 4) +
    (2 * (inputCode source target fuel).length + 2) =
    10 * (inputCode source target fuel).length + 8 * cert.length + 6 by omega] at b
  rw [show ((2 * (4 * (inputCode source target fuel).length) + 2 * (4 * cert.length) + 4) +
    (2 * (inputCode source target fuel).length + 2)) +
    (2 * (inputCode source target fuel).length + 3) =
    12 * (inputCode source target fuel).length + 8 * cert.length + 9 by omega] at c
  rw [show (((2 * (4 * (inputCode source target fuel).length) + 2 * (4 * cert.length) + 4) +
    (2 * (inputCode source target fuel).length + 2)) +
    (2 * (inputCode source target fuel).length + 3)) + (2 * cert.length + 2) =
    12 * (inputCode source target fuel).length + 10 * cert.length + 11 by omega] at d
  exact ⟨a, b, c, d⟩

theorem malformed_frame_stops_before_both_decoders (raw : Bits)
    (malformed : BitPairFraming.unframe raw = none) :
    (next caller)^[BitPairFraming.runSteps raw] (some (entry regs raw ctx)) =
      some (cfg (some rejectLabel) (resetFramer regs) {} ctx) := by
  simpa only [runSteps, sourceOutcome, malformed, Nat.add_zero, resultCfg] using
    run_source caller regs raw ctx

theorem input_decode_failure_preserves_every_certificate_bit (input cert : Bits)
    (failed : (unpackWordRun input).1 = none) :
    (next caller)^[2 * input.length + 2 * cert.length + 4 + OpenDecoderMachine.runSteps input]
        (some (entry regs (frame input cert) ctx)) =
      some (cfg (some rejectLabel) (afterInputDecoder regs) { certificateBits := cert } ctx) := by
  simpa only [runSteps, sourceOutcome, BitPairFraming.unframe_frame,
    BitPairFraming.runSteps_frame, failed, Nat.add_zero, resultCfg] using
    run_source caller regs (frame input cert) ctx

theorem input_parse_failure_restores_the_complete_word (input : Word) (cert : Bits)
    (failed : (parseInputRun input).1 = none) :
    (next caller)^[8 * input.length + 2 * cert.length + 4 +
        (2 * input.length + 2 + InputParserMachine.inputSteps input)]
        (some (entry regs (frame (wordBits input) cert) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { inputRaw := input, certificateBits := cert } ctx) := by
  have run := run_source caller regs (frame (wordBits input) cert) ctx
  simp only [runSteps, sourceOutcome, BitPairFraming.unframe_frame,
    BitPairFraming.runSteps_frame, unpackWordRun_code, OpenDecoderMachine.runSteps_code,
    wordBits_length, failed, Nat.add_zero, resultCfg, decodedInputData] at run
  rw [show 2 * (4 * input.length) + 2 * cert.length + 4 +
    (2 * input.length + 2 + InputParserMachine.inputSteps input) =
    8 * input.length + 2 * cert.length + 4 +
    (2 * input.length + 2 + InputParserMachine.inputSteps input) by omega] at run
  exact run

theorem certificate_failure_occurs_after_the_actual_input_success
    (source target : BinaryTree Unit) (fuel cert : Bits)
    (failed : (unpackWordRun cert).1 = none) :
    (next caller)^[12 * (inputCode source target fuel).length + 2 * cert.length + 9 +
        OpenDecoderMachine.runSteps cert]
        (some (entry regs (frame (wordBits (inputCode source target fuel)) cert) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel } ctx) := by
  have count := InputParserMachine.inputSteps_of_some (inputCode source target fuel)
    source target fuel (congrArg Prod.fst (parseInputRun_code source target fuel))
  have run := run_source caller regs (frame (wordBits (inputCode source target fuel)) cert) ctx
  simp only [runSteps, sourceOutcome, BitPairFraming.unframe_frame,
    BitPairFraming.runSteps_frame, unpackWordRun_code, OpenDecoderMachine.runSteps_code,
    wordBits_length, parseInputRun_code, count, failed, resultCfg, parsedData] at run
  rw [show 2 * (4 * (inputCode source target fuel).length) + 2 * cert.length + 4 +
    (2 * (inputCode source target fuel).length + 2 +
      (2 * (inputCode source target fuel).length + 3 + OpenDecoderMachine.runSteps cert)) =
    12 * (inputCode source target fuel).length + 2 * cert.length + 9 +
      OpenDecoderMachine.runSteps cert by omega] at run
  exact run

/-- Source suffix rejection restores all input tags and never begins certificate decoding. -/
theorem a_trailing_input_tag_returns_the_entire_original_word
    (source target : BinaryTree Unit) (fuel : Bits) (tag : Tag) (tail : Word) (cert : Bits) :
    (next caller)^[10 * (inputCode source target fuel ++ tag :: tail).length +
        2 * cert.length + 4 * (treeCode source).length +
        4 * (treeCode target).length + 4 * fuel.length + 24]
        (some (entry regs (frame (wordBits (inputCode source target fuel ++ tag :: tail)) cert) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { inputRaw := inputCode source target fuel ++ tag :: tail, certificateBits := cert } ctx) := by
  have run := input_parse_failure_restores_the_complete_word caller regs ctx
    (inputCode source target fuel ++ tag :: tail) cert
    (congrArg Prod.fst (parseInputRun_trailing source target fuel tag tail))
  rw [InputParserMachine.inputSteps_trailing source target fuel (tag :: tail) (List.cons_ne_nil _ _)] at run
  rw [show 8 * (inputCode source target fuel ++ tag :: tail).length + 2 * cert.length + 4 +
    (2 * (inputCode source target fuel ++ tag :: tail).length + 2 +
      (4 * (treeCode source).length + 4 * (treeCode target).length + 4 * fuel.length + 18)) =
    10 * (inputCode source target fuel ++ tag :: tail).length + 2 * cert.length +
      4 * (treeCode source).length + 4 * (treeCode target).length + 4 * fuel.length + 24 by omega] at run
  exact run

/-- The independent raw recognition theorem observes the complete first-return state. -/
theorem first_success_recognizes_exact_framed_fields (raw : Bits)
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    (next caller)^[runSteps raw] (some (entry regs raw ctx)) =
        some (cfg (some dispatchLabel) (reset regs)
          { sourceTree := treeCode source, targetTree := treeCode target,
            fuel := fuel, certificateWord := cert } ctx) ↔
      raw = frame (wordBits (inputCode source target fuel)) (wordBits cert) :=
  run_code_iff caller regs raw ctx source target fuel cert

/-- The same emitted binary lists are the actual machine input, with their source tariff separate. -/
theorem actual_packed_emitters_feed_the_composed_machine
    (source target : BinaryTree Unit) (fuel : Bits) (moves : List Trees.Rotations.RotationMove) :
    (next caller)^[12 * (inputCode source target fuel).length + 10 * (certCode moves).length + 11]
        (some (entry regs (frame (emitPackedInputRun source target fuel).1
          (emitPackedCertificateRun moves).1) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target,
          fuel := fuel, certificateWord := certCode moves } ctx) := by
  rw [emitPackedInputRun_value, emitPackedCertificateRun_value]
  exact run_code caller regs source target fuel (certCode moves) ctx

/-- The literal endpoints quantify arbitrary finite caller state and every outside store. -/
theorem the_fixed_early_failure_routes :
    (next caller)^[2] (some (entry regs [] ctx)) =
        some (cfg (some rejectLabel) (resetFramer regs) {} ctx) ∧
      (next caller)^[2] (some (entry regs [false] ctx)) =
        some (cfg (some rejectLabel) (resetFramer regs) {} ctx) ∧
      (next caller)^[14] (some (entry regs (frame [false] [false, true, true]) ctx)) =
        some (cfg (some rejectLabel) (afterInputDecoder regs)
          { certificateBits := [false, true, true] } ctx) ∧
      (next caller)^[17] (some (entry regs (frame [] [false, true, true]) ctx)) =
        some (cfg (some rejectLabel) (reset regs)
          { certificateBits := [false, true, true] } ctx) ∧
      (next caller)^[77] (some (entry regs
          (frame (wordBits (inputCode empty.val empty.val [])) [false, true, true]) ctx)) =
        some (cfg (some rejectLabel) (reset regs)
          { sourceTree := [emptyTag], targetTree := [emptyTag] } ctx) := by
  refine ⟨malformed_frame_stops_before_both_decoders caller regs ctx [] rfl,
    malformed_frame_stops_before_both_decoders caller regs ctx [false] rfl,
    input_decode_failure_preserves_every_certificate_bit caller regs ctx [false] [false, true, true] rfl,
    input_parse_failure_restores_the_complete_word caller regs ctx [] [false, true, true] rfl,
    certificate_failure_occurs_after_the_actual_input_success caller regs ctx
      empty.val empty.val [] [false, true, true] rfl⟩

theorem empty_equal_trees_return_before_any_fuel_inspection :
    (next caller)^[71]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) []) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [emptyTag], targetTree := [emptyTag] } ctx) :=
  run_code caller regs empty.val empty.val [] [] ctx

theorem the_one_rotation_fields_have_the_expected_199_step_route :
    (next caller)^[199]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits (certCode [rootRight]))) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0],
          fuel := [true], certificateWord := [7, 10] } ctx) :=
  run_code caller regs leftTwo.val rightTwo.val [true] (certCode [rootRight]) ctx

theorem reserved_certificate_syntax_is_not_rotation_acceptance :
    (next caller)^[189]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits [15])) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0],
          fuel := [true], certificateWord := [15] } ctx) ∧
      (parseMoveRun [15]).1 = none ∧
      (verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits [15])).1 = false := by
  refine ⟨run_code caller regs leftTwo.val rightTwo.val [true] [15] ctx, rfl, ?_⟩
  rw [verifyBitsRun_code_value, verifyRun_code,
    checkStreamRun_parse_failure [true] [false] leftTwo.val rightTwo.val 15 [] rfl rfl]

theorem unequal_trees_are_preserved_by_successful_syntax :
    (next caller)^[107]
        (some (entry regs (frame (wordBits (inputCode empty.val singleton.val [true])) []) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [0], targetTree := [1, 0, 0], fuel := [true] } ctx) ∧
      empty.val.numNodes ≠ singleton.val.numNodes ∧
      (verifyBitsRun (wordBits (inputCode empty.val singleton.val [true])) []).1 = false := by
  refine ⟨run_code caller regs empty.val singleton.val [true] [] ctx, by decide, ?_⟩
  change (verifyBitsRun (wordBits (inputCode empty.val singleton.val [true])) (wordBits ([] : Word))).1 = false
  rw [verifyBitsRun_code_value, verifyRun_code]
  exact Examples.RotationCertificateVerification.unequal_sizes_reject_every_certificate
    [true] empty.val singleton.val [] (by decide)

/-- These are all four real cumulative handoffs, not a detached addition of stage tariffs. -/
theorem the_one_rotation_route_has_cumulative_times_132_162_193_199 :
    (next caller)^[132]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits (certCode [rootRight]))) ctx)) =
      some (inputDecoderEntry regs (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight])) ctx) ∧
    (next caller)^[162]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits (certCode [rootRight]))) ctx)) =
      some (inputEntry regs (inputCode leftTwo.val rightTwo.val [true]) (wordBits (certCode [rootRight])) ctx) ∧
    (next caller)^[193]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits (certCode [rootRight]))) ctx)) =
      some (certificateDecoderEntry regs leftTwo.val rightTwo.val [true] (wordBits (certCode [rootRight])) ctx) ∧
    (next caller)^[199]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits (certCode [rootRight]))) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0],
          fuel := [true], certificateWord := [7, 10] } ctx) :=
  encoded_fields_have_all_four_actual_handoffs caller regs ctx leftTwo.val rightTwo.val
    [true] (certCode [rootRight])

theorem the_empty_route_has_cumulative_times_44_56_69_71 :
    (next caller)^[44]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) []) ctx)) =
      some (inputDecoderEntry regs (wordBits (inputCode empty.val empty.val [])) [] ctx) ∧
    (next caller)^[56]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) []) ctx)) =
      some (inputEntry regs (inputCode empty.val empty.val []) [] ctx) ∧
    (next caller)^[69]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) []) ctx)) =
      some (certificateDecoderEntry regs empty.val empty.val [] [] ctx) ∧
    (next caller)^[71]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) []) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [emptyTag], targetTree := [emptyTag] } ctx) :=
  encoded_fields_have_all_four_actual_handoffs caller regs ctx empty.val empty.val [] []

end Generic

theorem actual_raw_lengths_match_the_distinct_routes :
    (frame [false] [false, true, true]).length = 6 ∧
      (frame [] [false, true, true]).length = 4 ∧
      (frame (wordBits (inputCode empty.val empty.val [])) [false, true, true]).length = 44 ∧
      (frame (wordBits (inputCode empty.val empty.val [])) []).length = 41 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]))).length = 121 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val [true])) (wordBits [15])).length = 117 := by
  simp only [BitPairFraming.frame_length, wordBits_length]
  decide

/-- The six other borrowed observations stay stale when framing alone rejects. -/
theorem early_failure_resets_only_the_field_it_borrows (callerBit : Bool) :
    (next haltCaller)^[2] (some (entry (staleRegisters callerBit) [] sampleContext)) =
      some (cfg (some rejectLabel)
        ((some 15, some ()), ⟨none, some false, some true, some false, some 12⟩, callerBit)
        {} sampleContext) ∧
      resetFramer (staleRegisters callerBit) ≠ reset (staleRegisters callerBit) := by
  refine ⟨(the_fixed_early_failure_routes haltCaller (staleRegisters callerBit) sampleContext).1, ?_⟩
  intro equal
  have tree := congrArg (fun r : Registers Bool => r.1.1) equal
  cases tree

theorem input_decode_failure_retains_the_stale_tree_group (callerBit : Bool) :
    (next haltCaller)^[14]
        (some (entry (staleRegisters callerBit) (frame [false] [false, true, true]) sampleContext)) =
      some (cfg (some rejectLabel) ((some 15, some ()), BitDecoderMachine.zeroRegisters, callerBit)
        { certificateBits := [false, true, true] } sampleContext) :=
  (the_fixed_early_failure_routes haltCaller (staleRegisters callerBit) sampleContext).2.2.1

theorem full_success_really_resets_both_temporary_groups (callerBit : Bool) :
    (next haltCaller)^[199]
        (some (entry (staleRegisters callerBit)
          (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
            (wordBits (certCode [rootRight]))) sampleContext)) =
      some (cfg (some dispatchLabel) ((none, none), BitDecoderMachine.zeroRegisters, callerBit)
        { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0],
          fuel := [true], certificateWord := [7, 10] } sampleContext) :=
  the_one_rotation_fields_have_the_expected_199_step_route haltCaller (staleRegisters callerBit) sampleContext

section TransportedStorage
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

omit [DecidableEq K] in
/-- The complete static view permutes finite register fields and physical stack names. -/
theorem the_decoder_representation_is_a_real_reordering (data : LocalData) :
    inputDecoderCfg (Λ := Λ)
        (inputDecoderView (some (OpenDecoderMachine.phaseLabel .scan))
          (regs.2.1, regs.1, regs.2.2) data ctx) =
      cfg (some (inputDecoderLabel .scan)) regs data ctx ∧
      decoderStackEquiv (K := K) .input (.inl .input) = .inl .inputBits ∧
      decoderStackEquiv (K := K) .input (.inl .output) = .inl .inputRaw ∧
      decoderStackEquiv (K := K) .certificate (.inl .input) = .inl .certificateBits ∧
      decoderStackEquiv (K := K) .certificate (.inl .output) = .inl .certificateWord := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  have reordered : decoderRegisterEquiv (regs.2.1, regs.1, regs.2.2) = regs := by
    rcases regs with ⟨tree, decoder, callerState⟩
    rfl
  simpa only [Option.map_some, inputDecoderLabelEquiv_phase, reordered]
    using inputDecoderCfg_view (some (OpenDecoderMachine.phaseLabel .scan))
      (regs.2.1, regs.1, regs.2.2) data ctx

/-- Transport connects the actual generalized local scan, not merely a calculated count. -/
theorem dirty_framing_runs_in_the_installed_global_program (data : LocalData) :
    (next caller)^[OpenFramingMachine.scanSteps data.framedRaw
        data.frameFirstReverse data.frameCertReverse]
        (some (cfg (some (framerLabel .scanPrefix)) regs data ctx)) =
      some (match BitPairFraming.unframe data.framedRaw with
        | none => cfg (some rejectLabel) (resetFramer regs)
            { data with framedRaw := [], frameFirstReverse := [] } ctx
        | some pair => cfg (some (inputDecoderLabel .scan)) (resetFramer regs)
            { data with
              framedRaw := []
              frameFirstReverse := []
              frameCertReverse := []
              inputBits := data.frameFirstReverse.reverse ++ pair.1 ++ data.inputBits
              certificateBits := data.frameCertReverse.reverse ++ pair.2 ++ data.certificateBits } ctx) := by
  let localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R := fun _ => .halt
  let localRegs := framerRegisterEquiv.symm regs
  have restoredRegisters : framerRegisterEquiv localRegs = regs :=
    Equiv.apply_symm_apply _ _
  let localCtx := framerContext (Γ := Γ) data ctx
  let start : FramerCfg Γ Λ R := OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix))
    localRegs data.framedRaw data.frameFirstReverse data.frameCertReverse
      data.inputBits data.certificateBits localCtx
  have transported := framer_prefix_installed caller localCaller
    (OpenFramingMachine.scanSteps data.framedRaw data.frameFirstReverse data.frameCertReverse) start (by
      intro j strict
      obtain ⟨reached, executed, _, _, owned, _⟩ :=
        OpenFramingMachine.phase_prefix localCaller .scanPrefix data.framedRaw
          data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
          localRegs localCtx j (Nat.le_of_lt strict)
      exact ⟨reached, executed, owned.mp strict⟩)
  change (next caller)^[OpenFramingMachine.scanSteps data.framedRaw
      data.frameFirstReverse data.frameCertReverse]
      (some (framerCfg (framerView (some (OpenFramingMachine.phaseLabel .scanPrefix))
        localRegs data ctx))) = _ at transported
  rw [framerCfg_view, Option.map_some, framerLabelEquiv_phase,
    show framerRegisterEquiv localRegs = regs from Equiv.apply_symm_apply _ _] at transported
  rw [OpenFramingMachine.scanPrefix_iterate] at transported
  cases returned : BitPairFraming.unframe data.framedRaw with
  | none =>
      rw [returned] at transported
      change (next caller)^[_] _ = some (framerCfg
        (framerView (some (OpenFramingMachine.resultLabel .failure)) (OpenFramingMachine.reset localRegs)
          { data with framedRaw := [], frameFirstReverse := [] } ctx)) at transported
      simpa only [framerCfg_view, Option.map_some, framerLabelEquiv_failure,
        framerRegisterEquiv_reset, restoredRegisters] using transported
  | some pair =>
      rw [returned] at transported
      change (next caller)^[_] _ = some (framerCfg
        (framerView (some (OpenFramingMachine.resultLabel .success)) (OpenFramingMachine.reset localRegs)
          { data with
            framedRaw := []
            frameFirstReverse := []
            frameCertReverse := []
            inputBits := data.frameFirstReverse.reverse ++ pair.1 ++ data.inputBits
            certificateBits := data.frameCertReverse.reverse ++ pair.2 ++ data.certificateBits } ctx)) at transported
      simpa only [framerCfg_view, Option.map_some, framerLabelEquiv_success,
        framerRegisterEquiv_reset, restoredRegisters] using transported

/-- Old output is an actual suffix; a failed nibble discards only the reverse accumulator. -/
theorem dirty_input_decoding_runs_in_the_installed_global_program (data : LocalData) :
    (next caller)^[OpenDecoderMachine.runSteps data.inputBits + data.decodeReverse.length]
        (some (cfg (some (inputDecoderLabel .scan)) regs data ctx)) =
      some (match (unpackWordRun data.inputBits).1 with
        | none => cfg (some rejectLabel) (afterInputDecoder regs)
            { data with inputBits := [], decodeReverse := [] } ctx
        | some word => cfg (some (InputParserMachine.treeLabel .source .init)) (afterInputDecoder regs)
            { data with
              inputBits := []
              decodeReverse := []
              inputRaw := data.decodeReverse.reverse ++ word ++ data.inputRaw } ctx) := by
  let localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R :=
    fun _ => .halt
  let localRegs := decoderRegisterEquiv.symm regs
  have transportedReset : decoderRegisterEquiv (OpenDecoderMachine.reset localRegs) =
      afterInputDecoder regs := by
    rcases regs with ⟨tree, decoder, callerState⟩
    rfl
  have transported := inputDecoder_scan_installed caller localCaller data.inputBits data.decodeReverse
    data.inputRaw localRegs (decoderContext .input data ctx)
  change (next caller)^[_]
      (some (inputDecoderCfg (inputDecoderView (some (OpenDecoderMachine.phaseLabel .scan))
        localRegs data ctx))) = _ at transported
  rw [inputDecoderCfg_view, Option.map_some, inputDecoderLabelEquiv_phase,
    show decoderRegisterEquiv localRegs = regs from Equiv.apply_symm_apply _ _] at transported
  cases returned : (unpackWordRun data.inputBits).1 with
  | none =>
      rw [returned] at transported
      change (next caller)^[_] _ = some (inputDecoderCfg
        (inputDecoderView (some (OpenDecoderMachine.resultLabel .failure)) (OpenDecoderMachine.reset localRegs)
          { data with inputBits := [], decodeReverse := [] } ctx)) at transported
      simpa only [inputDecoderCfg_view, Option.map_some, inputDecoderLabelEquiv_failure,
        transportedReset] using transported
  | some word =>
      rw [returned] at transported
      change (next caller)^[_] _ = some (inputDecoderCfg
        (inputDecoderView (some (OpenDecoderMachine.resultLabel .success)) (OpenDecoderMachine.reset localRegs)
          { data with
            inputBits := []
            decodeReverse := []
            inputRaw := data.decodeReverse.reverse ++ word ++ data.inputRaw } ctx)) at transported
      simpa only [inputDecoderCfg_view, Option.map_some, inputDecoderLabelEquiv_success,
        transportedReset] using transported

/-- The second decoder uses distinct physical input/output stacks under the same transition function. -/
theorem dirty_certificate_decoding_runs_in_the_installed_global_program (data : LocalData) :
    (next caller)^[OpenDecoderMachine.runSteps data.certificateBits + data.decodeReverse.length]
        (some (cfg (some (certificateDecoderLabel .scan)) regs data ctx)) =
      some (match (unpackWordRun data.certificateBits).1 with
        | none => cfg (some rejectLabel) (afterInputDecoder regs)
            { data with certificateBits := [], decodeReverse := [] } ctx
        | some word => cfg (some dispatchLabel) (afterInputDecoder regs)
            { data with
              certificateBits := []
              decodeReverse := []
              certificateWord := data.decodeReverse.reverse ++ word ++ data.certificateWord } ctx) := by
  let localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) →
      CertificateDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := decoderRegisterEquiv.symm regs
  have transportedReset : decoderRegisterEquiv (OpenDecoderMachine.reset localRegs) =
      afterInputDecoder regs := by
    rcases regs with ⟨tree, decoder, callerState⟩
    rfl
  have transported := certificateDecoder_scan_installed caller localCaller data.certificateBits
    data.decodeReverse data.certificateWord localRegs (decoderContext .certificate data ctx)
  change (next caller)^[_]
      (some (certificateDecoderCfg (certificateDecoderView (some (OpenDecoderMachine.phaseLabel .scan))
        localRegs data ctx))) = _ at transported
  rw [certificateDecoderCfg_view, Option.map_some, certificateDecoderLabelEquiv_phase,
    show decoderRegisterEquiv localRegs = regs from Equiv.apply_symm_apply _ _] at transported
  cases returned : (unpackWordRun data.certificateBits).1 with
  | none =>
      rw [returned] at transported
      change (next caller)^[_] _ = some (certificateDecoderCfg
        (certificateDecoderView (some (OpenDecoderMachine.resultLabel .failure)) (OpenDecoderMachine.reset localRegs)
          { data with certificateBits := [], decodeReverse := [] } ctx)) at transported
      simpa only [certificateDecoderCfg_view, Option.map_some, certificateDecoderLabelEquiv_failure,
        transportedReset] using transported
  | some word =>
      rw [returned] at transported
      change (next caller)^[_] _ = some (certificateDecoderCfg
        (certificateDecoderView (some (OpenDecoderMachine.resultLabel .success)) (OpenDecoderMachine.reset localRegs)
          { data with
            certificateBits := []
            decodeReverse := []
            certificateWord := data.decodeReverse.reverse ++ word ++ data.certificateWord } ctx)) at transported
      simpa only [certificateDecoderCfg_view, Option.map_some, certificateDecoderLabelEquiv_success,
        transportedReset] using transported

/-- Every finite tag, including 11--15, is copied by the actual certificate decoder. -/
theorem every_tag_is_preserved_at_the_real_certificate_handoff
    (tag : Tag) (source target : BinaryTree Unit) (fuel : Bits) :
    (next caller)^[4]
        (some (certificateDecoderEntry regs source target fuel (wordBits [tag]) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target,
          fuel := fuel, certificateWord := [tag] } ctx) :=
  (the_certificate_decoder_returns_a_word_not_a_move_proof caller regs ctx source target fuel [tag]).run

theorem the_dirty_framer_preserves_both_old_output_suffixes :
    (next caller)^[18]
        (some (cfg (some (framerLabel .scanPrefix)) regs
          { framedRaw := frame [true, false] [false, true, true],
            frameFirstReverse := [true, false], frameCertReverse := [false, true],
            inputBits := [false], certificateBits := [true, false],
            inputRaw := [15], pending := [()], fuel := [false, true, false] } ctx)) =
      some (cfg (some (inputDecoderLabel .scan)) (resetFramer regs)
        { inputBits := [false, true, true, false, false],
          certificateBits := [true, false, false, true, true, true, false],
          inputRaw := [15], pending := [()], fuel := [false, true, false] } ctx) := by
  exact dirty_framing_runs_in_the_installed_global_program caller regs ctx
    { framedRaw := frame [true, false] [false, true, true],
      frameFirstReverse := [true, false], frameCertReverse := [false, true],
      inputBits := [false], certificateBits := [true, false],
      inputRaw := [15], pending := [()], fuel := [false, true, false] }

theorem malformed_dirty_framing_does_not_erase_other_storage :
    (next caller)^[8]
        (some (cfg (some (framerLabel .scanPrefix)) regs
          { framedRaw := escapeBits [true, false], frameFirstReverse := [true, false],
            frameCertReverse := [false, true], inputBits := [false], certificateBits := [true, false],
            certificateWord := [15, 2] } ctx)) =
      some (cfg (some rejectLabel) (resetFramer regs)
        { frameCertReverse := [false, true], inputBits := [false], certificateBits := [true, false],
          certificateWord := [15, 2] } ctx) ∧
    (next caller)^[8]
        (some (cfg (some (framerLabel .scanPrefix)) regs
          { framedRaw := escapeBits [true, false] ++ [false], frameFirstReverse := [true, false],
            frameCertReverse := [false, true], inputBits := [false], certificateBits := [true, false],
            certificateWord := [15, 2] } ctx)) =
      some (cfg (some rejectLabel) (resetFramer regs)
        { frameCertReverse := [false, true], inputBits := [false], certificateBits := [true, false],
          certificateWord := [15, 2] } ctx) :=
  ⟨dirty_framing_runs_in_the_installed_global_program caller regs ctx
      { framedRaw := escapeBits [true, false], frameFirstReverse := [true, false],
        frameCertReverse := [false, true], inputBits := [false], certificateBits := [true, false],
        certificateWord := [15, 2] },
    dirty_framing_runs_in_the_installed_global_program caller regs ctx
      { framedRaw := escapeBits [true, false] ++ [false], frameFirstReverse := [true, false],
        frameCertReverse := [false, true], inputBits := [false], certificateBits := [true, false],
        certificateWord := [15, 2] }⟩

theorem nonpalindromic_dirty_decoding_uses_two_distinct_physical_destinations :
    (next caller)^[8]
        (some (cfg (some (inputDecoderLabel .scan)) regs
          { inputBits := wordBits [3, 12], decodeReverse := [5, 9], inputRaw := [15, 2],
            certificateBits := [true, false, true], certificateWord := [11], fuel := [false, true] } ctx)) =
      some (cfg (some (InputParserMachine.treeLabel .source .init)) (afterInputDecoder regs)
        { inputRaw := [9, 5, 3, 12, 15, 2], certificateBits := [true, false, true],
          certificateWord := [11], fuel := [false, true] } ctx) ∧
    (next caller)^[8]
        (some (cfg (some (certificateDecoderLabel .scan)) regs
          { certificateBits := wordBits [3, 12], decodeReverse := [5, 9], certificateWord := [15, 2],
            inputBits := [false, true, true], inputRaw := [11], fuel := [false, true] } ctx)) =
      some (cfg (some dispatchLabel) (afterInputDecoder regs)
        { certificateWord := [9, 5, 3, 12, 15, 2], inputBits := [false, true, true],
          inputRaw := [11], fuel := [false, true] } ctx) :=
  ⟨dirty_input_decoding_runs_in_the_installed_global_program caller regs ctx
      { inputBits := wordBits [3, 12], decodeReverse := [5, 9], inputRaw := [15, 2],
        certificateBits := [true, false, true], certificateWord := [11], fuel := [false, true] },
    dirty_certificate_decoding_runs_in_the_installed_global_program caller regs ctx
      { certificateBits := wordBits [3, 12], decodeReverse := [5, 9], certificateWord := [15, 2],
        inputBits := [false, true, true], inputRaw := [11], fuel := [false, true] }⟩

theorem partial_dirty_decode_consumes_bits_but_retains_old_output :
    (next caller)^[8]
        (some (cfg (some (inputDecoderLabel .scan)) regs
          { inputBits := wordBits [3, 12] ++ [true, false], decodeReverse := [5, 9],
            inputRaw := [15, 2], certificateBits := [false, true, true] } ctx)) =
      some (cfg (some rejectLabel) (afterInputDecoder regs)
        { inputRaw := [15, 2], certificateBits := [false, true, true] } ctx) ∧
    (next caller)^[8]
        (some (cfg (some (certificateDecoderLabel .scan)) regs
          { certificateBits := wordBits [3, 12] ++ [false, true, true], decodeReverse := [5, 9],
            certificateWord := [15, 2], sourceTree := [0], fuel := [true, false] } ctx)) =
      some (cfg (some rejectLabel) (afterInputDecoder regs)
        { certificateWord := [15, 2], sourceTree := [0], fuel := [true, false] } ctx) :=
  ⟨dirty_input_decoding_runs_in_the_installed_global_program caller regs ctx
      { inputBits := wordBits [3, 12] ++ [true, false], decodeReverse := [5, 9],
        inputRaw := [15, 2], certificateBits := [false, true, true] },
    dirty_certificate_decoding_runs_in_the_installed_global_program caller regs ctx
      { certificateBits := wordBits [3, 12] ++ [false, true, true], decodeReverse := [5, 9],
        certificateWord := [15, 2], sourceTree := [0], fuel := [true, false] }⟩

end TransportedStorage

section Prefixes
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

/-- The second certificate store stays empty throughout input decoding, not just at its end. -/
theorem input_decoding_preserves_an_undecoded_certificate (input cert : Bits)
    (n : Nat) (bound : n ≤ OpenDecoderMachine.runSteps input) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (inputDecoderEntry regs input cert ctx)) = some reached) :
    reached.stk (.inl .certificateBits) = cert ∧ reached.stk (.inl .certificateWord) = [] := by
  refine ⟨inputDecoder_prefix_certificate caller regs input cert ctx n bound reached executed, ?_⟩
  obtain ⟨actual, localRun, globalRun⟩ := inputDecoder_prefix_lift caller regs input cert ctx n bound
  have same : inputDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  obtain ⟨_, preserved⟩ := OpenDecoderMachine.prefix_frame (fun _ => .halt)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (resetFramer regs)) input [] []
      (decoderContext .input (framedData input cert) ctx)) actual n (by
        simpa only [OpenDecoderMachine.remainingSteps, OpenDecoderMachine.cfg,
          OpenDecoderMachine.phaseLabel, OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound)
      localRun
  have projection : (inputDecoderCfg actual).stk (.inl .certificateWord) =
      actual.stk (.inr (.inl .otherWord)) := by
    change Transport.stackEquiv (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input)
      actual.stk (decoderStackEquiv .input (.inr (.inl .otherWord))) = _
    rw [Transport.stackEquiv_apply]
    change List.map id _ = _
    simp
  rw [← same, projection]
  exact preserved (.inl .otherWord)

/-- Even parser rollback preserves the complete undecoded certificate and its empty Tag destination. -/
theorem input_parsing_preserves_an_undecoded_certificate (input : Word) (cert : Bits)
    (n : Nat) (bound : n ≤ InputParserMachine.inputSteps input) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (inputEntry regs input cert ctx)) = some reached) :
    reached.stk (.inl .certificateBits) = cert ∧ reached.stk (.inl .certificateWord) = [] := by
  refine ⟨input_prefix_certificate caller regs input cert ctx n bound reached executed, ?_⟩
  obtain ⟨actual, localRun, globalRun⟩ := input_prefix_lift caller regs input cert ctx n bound
  have same : inputCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  obtain ⟨_, preserved, _, _⟩ := InputParserMachine.prefix_preserves (fun _ => .halt) input
    (inputRegisterEquiv.symm (afterInputDecoder regs))
    (inputContext (decodedInputData input cert) ctx) n bound actual localRun
  have projection : (inputCfg actual).stk (.inl .certificateWord) =
      actual.stk (InputParserMachine.protectedStack (.inl .certificateWord)) := by
    change Transport.stackEquiv inputStackEquiv (inputSymbolEquiv (Γ := Γ))
      actual.stk (inputStackEquiv (InputParserMachine.protectedStack (.inl .certificateWord))) = _
    rw [Transport.stackEquiv_apply]
    change List.map id _ = _
    simp
  rw [← same, projection]
  exact preserved (.inl .certificateWord)

/-- These are global prefixes from the actual frame, after its physical certificate copying. -/
theorem framed_input_decode_prefixes_leave_the_certificate_undecoded
    (input cert : Bits) (n : Nat) (bound : n ≤ OpenDecoderMachine.runSteps input) :
    ∃ reached : Cfg Γ Λ R,
      (next caller)^[2 * input.length + 2 * cert.length + 4 + n]
        (some (entry regs (frame input cert) ctx)) = some reached ∧
      reached.stk (.inl .certificateBits) = cert ∧ reached.stk (.inl .certificateWord) = [] := by
  obtain ⟨actual, _, localRun⟩ := inputDecoder_prefix_lift caller regs input cert ctx n bound
  refine ⟨inputDecoderCfg actual,
    iterate_trans caller (framing_returns_the_actual_two_fields caller regs ctx input cert).run localRun, ?_⟩
  exact input_decoding_preserves_an_undecoded_certificate caller regs ctx input cert n bound _ localRun

theorem framed_input_parse_prefixes_leave_the_certificate_undecoded
    (input : Word) (cert : Bits) (n : Nat) (bound : n ≤ InputParserMachine.inputSteps input) :
    ∃ reached : Cfg Γ Λ R,
      (next caller)^[10 * input.length + 2 * cert.length + 6 + n]
        (some (entry regs (frame (wordBits input) cert) ctx)) = some reached ∧
      reached.stk (.inl .certificateBits) = cert ∧ reached.stk (.inl .certificateWord) = [] := by
  obtain ⟨actual, _, localRun⟩ := input_prefix_lift caller regs input cert ctx n bound
  have prior := (Trace.trans caller
    (framing_returns_the_actual_two_fields caller regs ctx (wordBits input) cert)
    (the_input_decoder_returns_the_actual_word caller regs ctx input cert)).run
  have reached := iterate_trans caller prior localRun
  simp only [wordBits_length] at reached
  have count : (2 * (4 * input.length) + 2 * cert.length + 4 + (2 * input.length + 2)) + n =
      10 * input.length + 2 * cert.length + 6 + n := by omega
  rw [count] at reached
  exact ⟨inputCfg actual, reached,
    input_parsing_preserves_an_undecoded_certificate caller regs ctx input cert n bound _ localRun⟩

theorem all_actual_prefixes_keep_their_caller_context [Fintype K]
    (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached : Cfg Γ Λ R,
      (next caller)^[n] (some (entry regs raw ctx)) = some reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ raw.length + contextCells ctx := by
  obtain ⟨reached, executed, owned⟩ := run_prefix caller regs raw ctx n bound
  obtain ⟨callerState, storesPreserved⟩ := prefix_context caller regs raw ctx n bound reached executed
  exact ⟨reached, executed, owned, callerState, storesPreserved,
    prefix_stackCells_le caller regs raw ctx n bound reached executed⟩

theorem the_global_bound_is_attained_at_an_actual_prefix [Fintype K] (raw : Bits) :
    (next caller)^[0] (some (entry regs raw ctx)) = some (entry regs raw ctx) ∧
      stackCells (entry (Λ := Λ) regs raw ctx) = raw.length + contextCells ctx :=
  zero_prefix_space_sharp caller regs raw ctx

theorem every_first_exit_is_at_the_declared_total
    (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached)
    (returned : ¬ Owned reached.l) :
    n = runSteps raw :=
  first_return_exact caller regs raw ctx n bound reached executed returned

theorem arbitrary_callers_agree_through_the_same_first_exit
    (other : External Λ → Statement Γ Λ R) (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    (next caller)^[n] (some (entry regs raw ctx)) =
      (next other)^[n] (some (entry regs raw ctx)) :=
  run_prefix_caller_independent caller other regs raw ctx n bound

/-- Uniform timed data and any continuation concern the identical program and endpoint. -/
def allRawInLinearTime (raw : Bits) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs ctx (sourceOutcome raw))) (8 * raw.length + 13) :=
  runTimedLinear caller regs raw ctx

def appendActualContinuation (raw : Bits) (extra : Nat) (finish : Option (Cfg Γ Λ R))
    (continuation : StateTransition.EvalsToInTime (step caller)
      (resultCfg regs ctx (sourceOutcome raw)) finish extra) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx) finish
      (extra + (8 * raw.length + 13)) :=
  StateTransition.EvalsToInTime.trans (step caller) (8 * raw.length + 13) extra
    (entry regs raw ctx) (resultCfg regs ctx (sourceOutcome raw)) finish
    (allRawInLinearTime caller regs ctx raw) continuation

end Prefixes

def fuelNine : Bits := [true, false, false, true, false]
def fuelNineWide : Bits := [true, false, false, true, false, false, false]

section Width
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

theorem equal_numeric_fuel_keeps_distinct_literal_execution_results :
    value fuelNine = 9 ∧ value fuelNineWide = 9 ∧
    (next caller)^[151]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val fuelNine))
          (wordBits [7, 10])) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [0], targetTree := [0], fuel := fuelNine, certificateWord := [7, 10] } ctx) ∧
    (next caller)^[175]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val fuelNineWide))
          (wordBits [7, 10])) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [0], targetTree := [0], fuel := fuelNineWide, certificateWord := [7, 10] } ctx) ∧
    resultCfg (Λ := Λ) regs ctx (.success empty.val empty.val fuelNine [7, 10]) ≠
      resultCfg regs ctx (.success empty.val empty.val fuelNineWide [7, 10]) := by
  refine ⟨rfl, rfl, run_code caller regs empty.val empty.val fuelNine [7, 10] ctx,
    run_code caller regs empty.val empty.val fuelNineWide [7, 10] ctx, ?_⟩
  intro same
  have lengths := congrArg (fun c : Cfg Γ Λ R => (c.stk (.inl .fuel)).length) same
  change 5 = 7 at lengths
  omega

theorem high_zero_width_changes_success_and_rollback_by_different_amounts :
    (next caller)^[178]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val fuelNine ++ [15]))
          (wordBits [7, 10])) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { inputRaw := inputCode empty.val empty.val fuelNine ++ [15],
          certificateBits := wordBits [7, 10] } ctx) ∧
    (next caller)^[206]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val fuelNineWide ++ [15]))
          (wordBits [7, 10])) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { inputRaw := inputCode empty.val empty.val fuelNineWide ++ [15],
          certificateBits := wordBits [7, 10] } ctx) :=
  ⟨a_trailing_input_tag_returns_the_entire_original_word caller regs ctx
      empty.val empty.val fuelNine 15 [] (wordBits [7, 10]),
    a_trailing_input_tag_returns_the_entire_original_word caller regs ctx
      empty.val empty.val fuelNineWide 15 [] (wordBits [7, 10])⟩

/-- Appending a partial certificate changes its framing cost, then rejects after actual input parsing. -/
theorem an_extra_certificate_bit_is_consumed_before_the_front_end_rejects (bit : Bool) :
    (next caller)^[201]
        (some (entry regs (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
          (wordBits (certCode [rootRight]) ++ [bit])) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0], fuel := [true] } ctx) ∧
      verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]) ++ [bit]) = (false, 112) := by
  refine ⟨?_, Examples.RotationCertificateBinary.valid_move_bits_then_partial_block bit⟩
  have failed := congrArg Prod.fst
    (unpackWordRun_partial (certCode [rootRight]) [bit] (by simp) (by simp))
  have run := certificate_failure_occurs_after_the_actual_input_success caller regs ctx
    leftTwo.val rightTwo.val [true] (wordBits (certCode [rootRight]) ++ [bit]) failed
  have count : 12 * (inputCode leftTwo.val rightTwo.val [true]).length +
      2 * (wordBits (certCode [rootRight]) ++ [bit]).length + 9 +
      OpenDecoderMachine.runSteps (wordBits (certCode [rootRight]) ++ [bit]) = 201 := by
    simp only [OpenDecoderMachine.runSteps, List.length_append, wordBits_length,
      List.length_cons, List.length_nil]
    rfl
  have sourceCode : treeCode leftTwo.val = [1, 1, 0, 0, 0] := rfl
  have targetCode : treeCode rightTwo.val = [1, 0, 1, 0, 0] := rfl
  simpa only [count, sourceCode, targetCode] using run

end Width

theorem high_zeros_change_bit_lengths_and_not_the_numeric_fuel :
    (frame (wordBits (inputCode empty.val empty.val fuelNine)) (wordBits [7, 10])).length = 89 ∧
      (frame (wordBits (inputCode empty.val empty.val fuelNineWide)) (wordBits [7, 10])).length = 105 ∧
      (frame (wordBits (inputCode empty.val empty.val fuelNine ++ [15])) (wordBits [7, 10])).length = 97 ∧
      (frame (wordBits (inputCode empty.val empty.val fuelNineWide ++ [15])) (wordBits [7, 10])).length = 113 ∧
      parseInputRun (inputCode empty.val empty.val fuelNine) =
        (some (empty.val, empty.val, fuelNine), 30) ∧
      parseInputRun (inputCode empty.val empty.val fuelNine ++ [15]) = (none, 30) ∧
      parseInputRun (inputCode empty.val empty.val fuelNineWide) =
        (some (empty.val, empty.val, fuelNineWide), 36) ∧
      parseInputRun (inputCode empty.val empty.val fuelNineWide ++ [15]) = (none, 36) := by
  refine ⟨rfl, rfl, rfl, rfl, parseInputRun_code _ _ _,
    parseInputRun_trailing _ _ _ 15 [], parseInputRun_code _ _ _, parseInputRun_trailing _ _ _ 15 []⟩

section TimedFourStages
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

/-- Four Type-valued runs compose through the same three physical intermediate states. -/
def encodedRouteInTime (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs (frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)
      (some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target,
          fuel := fuel, certificateWord := cert } ctx))
      ((2 * cert.length + 2) + ((2 * (inputCode source target fuel).length + 3) +
        ((2 * (inputCode source target fuel).length + 2) +
          (2 * (wordBits (inputCode source target fuel)).length +
            2 * (wordBits cert).length + 4)))) := by
  let start : Cfg Γ Λ R := entry regs (frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx
  let first : Cfg Γ Λ R := inputDecoderEntry regs (wordBits (inputCode source target fuel)) (wordBits cert) ctx
  let second : Cfg Γ Λ R := inputEntry regs (inputCode source target fuel) (wordBits cert) ctx
  let third : Cfg Γ Λ R := certificateDecoderEntry regs source target fuel (wordBits cert) ctx
  let finish : Cfg Γ Λ R := cfg (some dispatchLabel) (reset regs)
    { sourceTree := treeCode source, targetTree := treeCode target,
      fuel := fuel, certificateWord := cert } ctx
  let framing : StateTransition.EvalsToInTime (step caller) start (some first)
      (2 * (wordBits (inputCode source target fuel)).length + 2 * (wordBits cert).length + 4) :=
    { steps := 2 * (wordBits (inputCode source target fuel)).length + 2 * (wordBits cert).length + 4
      evals_in_steps := (framing_returns_the_actual_two_fields caller regs ctx
        (wordBits (inputCode source target fuel)) (wordBits cert)).run
      steps_le_m := Nat.le_refl _ }
  let decoding : StateTransition.EvalsToInTime (step caller) first (some second)
      (2 * (inputCode source target fuel).length + 2) :=
    { steps := 2 * (inputCode source target fuel).length + 2
      evals_in_steps := (the_input_decoder_returns_the_actual_word caller regs ctx
        (inputCode source target fuel) (wordBits cert)).run
      steps_le_m := Nat.le_refl _ }
  let parsing : StateTransition.EvalsToInTime (step caller) second (some third)
      (2 * (inputCode source target fuel).length + 3) :=
    { steps := 2 * (inputCode source target fuel).length + 3
      evals_in_steps := (the_input_parser_returns_actual_fields caller regs ctx source target fuel
        (wordBits cert)).run
      steps_le_m := Nat.le_refl _ }
  let certificate : StateTransition.EvalsToInTime (step caller) third (some finish)
      (2 * cert.length + 2) :=
    { steps := 2 * cert.length + 2
      evals_in_steps := (the_certificate_decoder_returns_a_word_not_a_move_proof
        caller regs ctx source target fuel cert).run
      steps_le_m := Nat.le_refl _ }
  exact StateTransition.EvalsToInTime.trans (step caller) _ _ start third (some finish)
    (StateTransition.EvalsToInTime.trans (step caller) _ _ start second (some third)
      (StateTransition.EvalsToInTime.trans (step caller) _ _ start first (some second) framing decoding)
      parsing) certificate

theorem the_constructed_four_stage_record_uses_199_actual_steps :
    (encodedRouteInTime caller regs ctx leftTwo.val rightTwo.val [true] (certCode [rootRight])).steps = 199 ∧
      (next caller)^[199]
        (some (entry regs (frame (emitPackedInputRun leftTwo.val rightTwo.val [true]).1
          (emitPackedCertificateRun [rootRight]).1) ctx)) =
      some (cfg (some dispatchLabel) (reset regs)
        { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0],
          fuel := [true], certificateWord := [7, 10] } ctx) := by
  refine ⟨rfl, ?_⟩
  rw [emitPackedInputRun_value, emitPackedCertificateRun_value]
  exact (encodedRouteInTime caller regs ctx leftTwo.val rightTwo.val [true]
    (certCode [rootRight])).evals_in_steps

end TimedFourStages

def frontExitLabel : TreeParserMachine.Result → Label Unit
  | .success => dispatchLabel
  | .failure => rejectLabel

/-- A concrete finite caller action, invoked only after either global live return. -/
def sentinelCaller (written : Bool) : External Unit → Statement SmallAlphabet Unit Bool
  | .inl _ => .push (.inr false) (fun _ => written) .halt
  | .inr _ => .halt

theorem sentinel_push_is_one_actual_later_transition
    (written : Bool) (result : TreeParserMachine.Result) (regs : Registers Bool)
    (data : LocalData) (bits : Bits) (tags : Word) :
    step (sentinelCaller written) (cfg (some (frontExitLabel result)) regs data (smallContext bits tags)) =
      some (cfg none regs data (smallContext (written :: bits) tags)) := by
  cases result <;> apply congrArg some <;> apply cfg_ext
  all_goals first
    | rfl
    | (funext slot; cases slot with
        | inl slot => cases slot <;> rfl
        | inr slot => cases slot <;> rfl)

def sentinelSuccessStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  entry (staleRegisters flag) (frame (wordBits (inputCode empty.val empty.val [])) [])
    (smallContext bits tags)

def sentinelSuccessHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some dispatchLabel) (reset (staleRegisters flag))
    { sourceTree := [0], targetTree := [0] } (smallContext bits tags)

def sentinelSuccessAfterCaller (written flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none (reset (staleRegisters flag))
    { sourceTree := [0], targetTree := [0] } (smallContext (written :: bits) tags)

def sentinelFailureStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  entry (staleRegisters flag) [] (smallContext bits tags)

def sentinelFailureHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some rejectLabel) (resetFramer (staleRegisters flag)) {} (smallContext bits tags)

def sentinelFailureAfterCaller (written flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none (resetFramer (staleRegisters flag)) {} (smallContext (written :: bits) tags)

def sentinelSuccessInTime (written flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller written)) (sentinelSuccessStart flag bits tags)
      (some (sentinelSuccessHandoff flag bits tags)) 71 where
  steps := 71
  evals_in_steps := empty_equal_trees_return_before_any_fuel_inspection
    (sentinelCaller written) (staleRegisters flag) (smallContext bits tags)
  steps_le_m := Nat.le_refl _

def sentinelFailureInTime (written flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller written)) (sentinelFailureStart flag bits tags)
      (some (sentinelFailureHandoff flag bits tags)) 2 where
  steps := 2
  evals_in_steps := (the_fixed_early_failure_routes
    (sentinelCaller written) (staleRegisters flag) (smallContext bits tags)).1
  steps_le_m := Nat.le_refl _

def sentinelSuccessCallerInTime (written flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller written)) (sentinelSuccessHandoff flag bits tags)
      (some (sentinelSuccessAfterCaller written flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_push_is_one_actual_later_transition written .success
    (reset (staleRegisters flag)) { sourceTree := [0], targetTree := [0] } bits tags
  steps_le_m := Nat.le_refl _

def sentinelFailureCallerInTime (written flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller written)) (sentinelFailureHandoff flag bits tags)
      (some (sentinelFailureAfterCaller written flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_push_is_one_actual_later_transition written .failure
    (resetFramer (staleRegisters flag)) {} bits tags
  steps_le_m := Nat.le_refl _

def sentinelSuccessCompositionInTime (written flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller written)) (sentinelSuccessStart flag bits tags)
      (some (sentinelSuccessAfterCaller written flag bits tags)) 72 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller written)) 71 1
    (sentinelSuccessStart flag bits tags) (sentinelSuccessHandoff flag bits tags)
    (some (sentinelSuccessAfterCaller written flag bits tags))
    (sentinelSuccessInTime written flag bits tags) (sentinelSuccessCallerInTime written flag bits tags)

def sentinelFailureCompositionInTime (written flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller written)) (sentinelFailureStart flag bits tags)
      (some (sentinelFailureAfterCaller written flag bits tags)) 3 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller written)) 2 1
    (sentinelFailureStart flag bits tags) (sentinelFailureHandoff flag bits tags)
    (some (sentinelFailureAfterCaller written flag bits tags))
    (sentinelFailureInTime written flag bits tags) (sentinelFailureCallerInTime written flag bits tags)

theorem success_handoff_halt_and_outer_none_are_different (written flag : Bool) (bits : Bits) (tags : Word) :
    (next (sentinelCaller written))^[71] (some (sentinelSuccessStart flag bits tags)) =
        some (sentinelSuccessHandoff flag bits tags) ∧
      (sentinelSuccessHandoff flag bits tags).stk (.inr false) = bits ∧
      (next (sentinelCaller written))^[72] (some (sentinelSuccessStart flag bits tags)) =
        some (sentinelSuccessAfterCaller written flag bits tags) ∧
      (sentinelSuccessAfterCaller written flag bits tags).l = none ∧
      (sentinelSuccessAfterCaller written flag bits tags).stk (.inr false) = written :: bits ∧
      (next (sentinelCaller written))^[73] (some (sentinelSuccessStart flag bits tags)) = none := by
  have halted : (next (sentinelCaller written))^[72] (some (sentinelSuccessStart flag bits tags)) =
      some (sentinelSuccessAfterCaller written flag bits tags) :=
    (sentinelSuccessCompositionInTime written flag bits tags).evals_in_steps
  refine ⟨(sentinelSuccessInTime written flag bits tags).evals_in_steps, rfl, halted, rfl, rfl, ?_⟩
  rw [show 73 = 72 + 1 by decide, Function.iterate_succ_apply', halted]
  rfl

theorem failure_handoff_halt_and_outer_none_are_different (written flag : Bool) (bits : Bits) (tags : Word) :
    (next (sentinelCaller written))^[2] (some (sentinelFailureStart flag bits tags)) =
        some (sentinelFailureHandoff flag bits tags) ∧
      (sentinelFailureHandoff flag bits tags).stk (.inr true) = tags ∧
      (next (sentinelCaller written))^[3] (some (sentinelFailureStart flag bits tags)) =
        some (sentinelFailureAfterCaller written flag bits tags) ∧
      (sentinelFailureAfterCaller written flag bits tags).l = none ∧
      (sentinelFailureAfterCaller written flag bits tags).stk (.inr false) = written :: bits ∧
      (next (sentinelCaller written))^[4] (some (sentinelFailureStart flag bits tags)) = none := by
  have halted : (next (sentinelCaller written))^[3] (some (sentinelFailureStart flag bits tags)) =
      some (sentinelFailureAfterCaller written flag bits tags) :=
    (sentinelFailureCompositionInTime written flag bits tags).evals_in_steps
  refine ⟨(sentinelFailureInTime written flag bits tags).evals_in_steps, rfl, halted, rfl, rfl, ?_⟩
  rw [show 4 = 3 + 1 by decide, Function.iterate_succ_apply', halted]
  rfl

theorem different_callers_agree_until_the_handoff_and_then_write_different_bits
    (flag : Bool) (bits : Bits) (tags : Word) :
    (∀ n, n ≤ 71 →
      (next (sentinelCaller true))^[n] (some (sentinelSuccessStart flag bits tags)) =
        (next (sentinelCaller false))^[n] (some (sentinelSuccessStart flag bits tags))) ∧
      step (sentinelCaller true) (sentinelSuccessHandoff flag bits tags) ≠
        step (sentinelCaller false) (sentinelSuccessHandoff flag bits tags) := by
  refine ⟨?_, ?_⟩
  · intro n bound
    exact run_prefix_caller_independent (sentinelCaller true) (sentinelCaller false)
      (staleRegisters flag) (frame (wordBits (inputCode empty.val empty.val [])) [])
      (smallContext bits tags) n bound
  · have trueStep : step (sentinelCaller true) (sentinelSuccessHandoff flag bits tags) =
        some (sentinelSuccessAfterCaller true flag bits tags) :=
      sentinel_push_is_one_actual_later_transition true .success
        (reset (staleRegisters flag)) { sourceTree := [0], targetTree := [0] } bits tags
    have falseStep : step (sentinelCaller false) (sentinelSuccessHandoff flag bits tags) =
        some (sentinelSuccessAfterCaller false flag bits tags) :=
      sentinel_push_is_one_actual_later_transition false .success
        (reset (staleRegisters flag)) { sourceTree := [0], targetTree := [0] } bits tags
    rw [trueStep, falseStep]
    intro same
    have stack := congrArg (fun c : Cfg SmallAlphabet Unit Bool => c.stk (.inr false))
      (Option.some.inj same)
    have head := (List.cons.inj stack).1
    cases head

/-- One real caller allocation already violates an incorrectly extended raw-length bound. -/
theorem the_uniform_space_bound_ends_before_caller_allocation :
    (∀ n, n ≤ 2 → ∀ reached : Cfg SmallAlphabet Unit Bool,
      (next (sentinelCaller true))^[n]
        (some (sentinelFailureStart true [false, true, false] [15, 6, 1])) = some reached →
        stackCells reached ≤ 6) ∧
      (next (sentinelCaller true))^[3]
        (some (sentinelFailureStart true [false, true, false] [15, 6, 1])) =
        some (sentinelFailureAfterCaller true true [false, true, false] [15, 6, 1]) ∧
      stackCells (sentinelFailureAfterCaller true true [false, true, false] [15, 6, 1]) = 7 := by
  refine ⟨?_, (sentinelFailureCompositionInTime true true _ _).evals_in_steps, ?_⟩
  · intro n bound reached executed
    have cells := prefix_stackCells_le (sentinelCaller true) (staleRegisters true) []
      (smallContext [false, true, false] [15, 6, 1]) n bound reached executed
    have total : ([] : Bits).length + contextCells (smallContext [false, true, false] [15, 6, 1]) = 6 := by decide
    simpa only [total] using cells
  · rw [sentinelFailureAfterCaller, stackCells_cfg]
    decide

def misleadingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => .goto (fun _ => dispatchLabel)
  | .inl .success => .halt
  | .inr _ => .halt

/-- A later dispatch label manufactured by caller code cannot recognize malformed raw input. -/
theorem eventual_dispatch_is_not_a_first_success_specification :
    (next misleadingCaller)^[2] (some (entry (staleRegisters true) [] sampleContext)) =
        some (cfg (some rejectLabel) (resetFramer (staleRegisters true)) {} sampleContext) ∧
      (next misleadingCaller)^[3] (some (entry (staleRegisters true) [] sampleContext)) =
        some (cfg (some dispatchLabel) (resetFramer (staleRegisters true)) {} sampleContext) ∧
      ∀ source target fuel cert,
        (next misleadingCaller)^[runSteps []] (some (entry (staleRegisters true) [] sampleContext)) ≠
          some (resultCfg (staleRegisters true) sampleContext (.success source target fuel cert)) := by
  have first := (the_fixed_early_failure_routes misleadingCaller (staleRegisters true) sampleContext).1
  have jump : (next misleadingCaller)^[1]
      (some (cfg (some rejectLabel) (resetFramer (staleRegisters true)) {} sampleContext)) =
      some (cfg (some dispatchLabel) (resetFramer (staleRegisters true)) {} sampleContext) := rfl
  refine ⟨first, iterate_trans misleadingCaller first jump, ?_⟩
  intro source target fuel cert claimed
  have code := (run_code_iff misleadingCaller (staleRegisters true) [] sampleContext
    source target fuel cert).mp claimed
  have lengths := congrArg List.length code
  rw [List.length_nil, BitPairFraming.frame_length] at lengths
  omega

/-- Only the empty-certificate inspection edge is supplied by this concrete finite continuation. -/
def emptyCertificateInspectCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .success =>
      .peek (.inl .certificateWord)
        (fun regs observed => (regs.1, { regs.2.1 with tag := observed }, regs.2.2))
        (.branch (fun regs => regs.2.1.tag.isNone)
          (.goto (fun _ => callerLabel ()))
          (.goto (fun _ => rejectLabel)))
  | .inl .failure => .halt
  | .inr _ => .halt

/-- The one-step inspection reaches a live future equality entry; no equality body has executed. -/
theorem empty_certificate_inspection_is_one_separate_actual_transition (flag : Bool) (bits : Bits) (tags : Word) :
    (next emptyCertificateInspectCaller)^[71] (some (sentinelSuccessStart flag bits tags)) =
        some (sentinelSuccessHandoff flag bits tags) ∧
      (next emptyCertificateInspectCaller)^[72] (some (sentinelSuccessStart flag bits tags)) =
        some (cfg (some (callerLabel ())) (reset (staleRegisters flag))
          { sourceTree := [0], targetTree := [0] } (smallContext bits tags)) := by
  have first : (next emptyCertificateInspectCaller)^[71] (some (sentinelSuccessStart flag bits tags)) =
      some (sentinelSuccessHandoff flag bits tags) :=
    empty_equal_trees_return_before_any_fuel_inspection emptyCertificateInspectCaller
      (staleRegisters flag) (smallContext bits tags)
  have inspect : (next emptyCertificateInspectCaller)^[1] (some (sentinelSuccessHandoff flag bits tags)) =
      some (cfg (some (callerLabel ())) (reset (staleRegisters flag))
        { sourceTree := [0], targetTree := [0] } (smallContext bits tags)) := rfl
  have continued := iterate_trans emptyCertificateInspectCaller
    (start := sentinelSuccessStart flag bits tags)
    (middle := sentinelSuccessHandoff flag bits tags)
    (finish := cfg (some (callerLabel ())) (reset (staleRegisters flag))
      { sourceTree := [0], targetTree := [0] } (smallContext bits tags))
    (first := 71) (second := 1) first inspect
  exact ⟨first, continued⟩

section ExactStageRegisters
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

/-- The zero prefix retains every stale field; positive framing prefixes reset only b0. -/
theorem framing_prefixes_have_the_exact_borrowed_register_effect (raw : Bits)
    (n : Nat) (bound : n ≤ BitPairFraming.runSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached) :
    reached.var = if n = 0 then regs else resetFramer regs := by
  by_cases zero : n = 0
  · subst n
    have same : entry regs raw ctx = reached := Option.some.inj executed
    rw [← same]
    rfl
  · rw [ite_eq_right zero]
    obtain ⟨actual, localRun, globalRun⟩ := framer_prefix_lift caller regs raw ctx n bound
    have same : framerCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
    let localRegs := framerRegisterEquiv.symm regs
    let localCtx := framerContext (Γ := Γ) {} ctx
    obtain ⟨observed, observedRun, _, path, _, cleared⟩ := OpenFramingMachine.run_prefix
      (fun _ => .halt) raw localRegs localCtx n bound
    have equal : observed = actual := Option.some.inj (observedRun.symm.trans localRun)
    subst observed
    have callerRegs := (OpenFramingMachine.local_reaches_preserves (fun _ => .halt) path).1
    have localReset : actual.var = OpenFramingMachine.reset localRegs :=
      Prod.ext (cleared (by omega)) callerRegs
    rw [← same]
    change framerRegisterEquiv actual.var = resetFramer regs
    rw [localReset, framerRegisterEquiv_reset]
    exact congrArg resetFramer (Equiv.apply_symm_apply framerRegisterEquiv regs)

/-- Decoding resets its own five fields after a positive prefix and preserves stale tree fields. -/
theorem input_decode_prefixes_have_the_exact_borrowed_register_effect (input cert : Bits)
    (n : Nat) (bound : n ≤ OpenDecoderMachine.runSteps input) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (inputDecoderEntry regs input cert ctx)) = some reached) :
    reached.var = if n = 0 then resetFramer regs else afterInputDecoder regs := by
  by_cases zero : n = 0
  · subst n
    have same : inputDecoderEntry regs input cert ctx = reached := Option.some.inj executed
    rw [← same]
    rfl
  · rw [ite_eq_right zero]
    obtain ⟨actual, localRun, globalRun⟩ := inputDecoder_prefix_lift caller regs input cert ctx n bound
    have same : inputDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
    let localRegs := decoderRegisterEquiv.symm (resetFramer regs)
    let localCtx := decoderContext (Γ := Γ) .input (framedData input cert) ctx
    have phaseBound : n ≤ OpenDecoderMachine.phaseSteps .scan input [] := by
      simpa only [OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound
    obtain ⟨observed, observedRun, _, path, _, cleared⟩ :=
      OpenDecoderMachine.phase_prefix (fun _ => .halt) .scan input [] [] localRegs localCtx n phaseBound
    have equal : observed = actual := Option.some.inj (observedRun.symm.trans localRun)
    subst observed
    have retained := (OpenDecoderMachine.local_reaches_frame (fun _ => .halt) path).1
    have localReset : actual.var = OpenDecoderMachine.reset localRegs :=
      Prod.ext (cleared (by omega)) retained
    rw [← same]
    change decoderRegisterEquiv actual.var = afterInputDecoder regs
    rw [localReset, decoderRegisterEquiv_reset]
    rfl

/-- The Input stage's actual first tree block resets the remaining borrowed tree pair. -/
theorem input_parse_prefixes_have_the_exact_borrowed_register_effect (input : Word) (cert : Bits)
    (n : Nat) (bound : n ≤ InputParserMachine.inputSteps input) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (inputEntry regs input cert ctx)) = some reached) :
    reached.var = if n = 0 then afterInputDecoder regs else reset regs := by
  obtain ⟨actual, localRun, globalRun⟩ := input_prefix_lift caller regs input cert ctx n bound
  have same : inputCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  have observed := (InputParserMachine.prefix_preserves (fun _ => .halt) input
    (inputRegisterEquiv.symm (afterInputDecoder regs))
    (inputContext (decodedInputData input cert) ctx) n bound actual localRun).1
  rw [← same]
  change actual.var = if n = 0 then afterInputDecoder regs else reset regs
  change actual.var = (if n = 0 then afterInputDecoder regs else reset regs) at observed
  exact observed

theorem the_installed_parser_really_allocates_a_pending_cell (input : Word) (cert : Bits) :
    (next caller)^[1] (some (inputEntry regs input cert ctx)) =
      some (cfg (some (InputParserMachine.treeLabel .source .scan)) (reset regs)
        { inputRaw := input, certificateBits := cert, pending := [()] } ctx) := by
  let localCaller : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R := fun _ => .halt
  let localRegs := inputRegisterEquiv.symm (afterInputDecoder regs)
  let localCtx := inputContext (Γ := Γ) (decodedInputData input cert) ctx
  let start : InputCfg Γ Λ R := InputParserMachine.entry localRegs input localCtx
  have localStep : (InputParserMachine.next localCaller)^[1] (some start) =
      some (InputParserMachine.cfg (some (InputParserMachine.treeLabel .source .scan))
        (InputParserMachine.reset localRegs) input [] [()] (InputParserMachine.treeOutputs [] []) [] [] localCtx) :=
    TreeParserMachine.init_step (InputParserMachine.handler localCaller) .source input [] [] localRegs
      (InputParserMachine.treeOutputs [] []) (InputParserMachine.stores [] [] localCtx)
  have transported := input_prefix_installed caller localCaller 1 start (by
    intro n strict
    have zero : n = 0 := by omega
    subst n
    exact ⟨start, rfl, True.intro⟩)
  rw [localStep] at transported
  change (next caller)^[1]
      (some (inputCfg (InputParserMachine.entry
        (inputRegisterEquiv.symm (afterInputDecoder regs)) input
        (inputContext (decodedInputData input cert) ctx)))) =
      some (inputCfg (inputView (some (InputParserMachine.treeLabel .source .scan))
        (InputParserMachine.reset localRegs)
        { inputRaw := input, certificateBits := cert, pending := [()] } ctx)) at transported
  rw [input_start_transport, inputCfg_view, Option.map_some] at transported
  exact transported

/-- A real delimiter pays for the parser's allocation even when the decoded input is empty. -/
theorem the_delimiter_pays_for_the_actual_empty_input_pending_cell [Fintype K] :
    (next caller)^[6] (some (entry regs [true] ctx)) = some (inputEntry regs [] [] ctx) ∧
      (next caller)^[7] (some (entry regs [true] ctx)) =
        some (cfg (some (InputParserMachine.treeLabel .source .scan)) (reset regs) { pending := [()] } ctx) ∧
      stackCells (inputEntry (Λ := Λ) regs [] [] ctx) = contextCells ctx ∧
      stackCells (cfg (some (InputParserMachine.treeLabel (Λ := ExtraLabel Λ) .source .scan))
        (reset regs) { pending := [()] } ctx) = 1 + contextCells ctx ∧
      (next caller)^[11] (some (entry regs [true] ctx)) =
        some (cfg (some rejectLabel) (reset regs) {} ctx) := by
  have prior := (Trace.trans caller
    (framing_returns_the_actual_two_fields caller regs ctx [] [])
    (the_input_decoder_returns_the_actual_word caller regs ctx [] [])).run
  have allocated := iterate_trans caller prior
    (the_installed_parser_really_allocates_a_pending_cell caller regs ctx [] [])
  refine ⟨prior, allocated, ?_, ?_, input_parse_failure_restores_the_complete_word caller regs ctx [] [] rfl⟩
  · rw [inputEntry, stackCells_cfg]
    simp only [localCells, decodedInputData, List.length_nil, Nat.add_zero, Nat.zero_add]
  · rw [stackCells_cfg]
    rfl

end ExactStageRegisters

/-- The entire fixed finite program is chosen before the raw input is supplied. -/
def concreteFrontEndMachine : Turing.FinTM2 := machine (sentinelCaller true) true

instance concreteFrontEndStackFintype : Fintype concreteFrontEndMachine.K :=
  concreteFrontEndMachine.kFin

instance concreteFrontEndLabelFintype : Fintype concreteFrontEndMachine.Λ :=
  concreteFrontEndMachine.ΛFin

instance concreteFrontEndRegisterFintype : Fintype concreteFrontEndMachine.σ :=
  concreteFrontEndMachine.σFin

theorem the_actual_finite_package_has_the_fixed_types_and_entry :
    Fintype.card concreteFrontEndMachine.K = 16 ∧
      Fintype.card concreteFrontEndMachine.Λ = 39 ∧
      Fintype.card concreteFrontEndMachine.σ = 93636 ∧
      concreteFrontEndMachine.k₀ = .inl .framedRaw ∧
      concreteFrontEndMachine.k₁ = .inl .certificateWord ∧
      concreteFrontEndMachine.main = framerLabel .scanPrefix ∧
      concreteFrontEndMachine.initialState = ((none, none), BitDecoderMachine.zeroRegisters, true) := by
  refine ⟨the_concrete_physical_types_have_the_fixed_finite_sizes.1,
    the_concrete_physical_types_have_the_fixed_finite_sizes.2.1,
    the_concrete_physical_types_have_the_fixed_finite_sizes.2.2.1, rfl, rfl, rfl, rfl⟩

theorem actual_finite_initialization_and_transition (raw : Bits) (state : Cfg SmallAlphabet Unit Bool) :
    Turing.initList concreteFrontEndMachine raw =
      entry ((none, none), BitDecoderMachine.zeroRegisters, true) raw (fun _ => []) ∧
      concreteFrontEndMachine.step state = step (sentinelCaller true) state :=
  ⟨initList_eq (sentinelCaller true) true raw, machine_step_eq (sentinelCaller true) true state⟩

def actualFiniteFrontEndInLinearTime (raw : Bits) :
    StateTransition.EvalsToInTime concreteFrontEndMachine.step
      (Turing.initList concreteFrontEndMachine raw)
      (some (resultCfg ((none, none), BitDecoderMachine.zeroRegisters, true)
        (fun _ : Bool => []) (sourceOutcome raw))) (8 * raw.length + 13) :=
  machineInTime (sentinelCaller true) true raw

theorem the_finite_timed_record_reaches_the_actual_source_endpoint (raw : Bits) :
    (actualFiniteFrontEndInLinearTime raw).steps = runSteps raw ∧
      (actualFiniteFrontEndInLinearTime raw).steps ≤ 8 * raw.length + 13 ∧
      (fun state : Option concreteFrontEndMachine.Cfg => state.bind concreteFrontEndMachine.step)^[runSteps raw]
        (some (Turing.initList concreteFrontEndMachine raw)) =
        some (resultCfg ((none, none), BitDecoderMachine.zeroRegisters, true)
          (fun _ : Bool => []) (sourceOutcome raw)) :=
  ⟨rfl, (actualFiniteFrontEndInLinearTime raw).steps_le_m,
    (actualFiniteFrontEndInLinearTime raw).evals_in_steps⟩

theorem every_actual_finite_machine_prefix_fits_the_raw_storage
    (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) (reached : concreteFrontEndMachine.Cfg)
    (executed : (fun state : Option concreteFrontEndMachine.Cfg =>
      state.bind concreteFrontEndMachine.step)^[n]
        (some (Turing.initList concreteFrontEndMachine raw)) = some reached) :
    stackCells reached ≤ raw.length :=
  machine_prefix_stackCells_le (sentinelCaller true) true raw n bound reached executed

/-- The selected output alphabet is Tag, but the actual endpoint remains a live configuration. -/
theorem the_finite_package_does_not_claim_an_output_only_halt (raw : Bits) :
    ∃ reached : concreteFrontEndMachine.Cfg,
      (fun state : Option concreteFrontEndMachine.Cfg => state.bind concreteFrontEndMachine.step)^[runSteps raw]
        (some (Turing.initList concreteFrontEndMachine raw)) = some reached ∧
      reached.l ≠ none ∧
      ∀ output : Word, reached ≠ Turing.haltList concreteFrontEndMachine output := by
  let reached : Cfg SmallAlphabet Unit Bool :=
    resultCfg ((none, none), BitDecoderMachine.zeroRegisters, true)
      (fun _ : Bool => []) (sourceOutcome raw)
  have executed :
      (fun state : Option concreteFrontEndMachine.Cfg => state.bind concreteFrontEndMachine.step)^[runSteps raw]
        (some (Turing.initList concreteFrontEndMachine raw)) = some reached :=
    (actualFiniteFrontEndInLinearTime raw).evals_in_steps
  have live : reached.l ≠ none := by
    dsimp only [reached]
    cases sourceOutcome raw <;> exact Option.some_ne_none _
  refine ⟨reached, executed, live, ?_⟩
  intro output equal
  apply live
  rw [equal]
  rfl

section FinalSeparators
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
  (ctx : ∀ k, List (Γ k))

/-- A noncanonical all-zero fuel list is retained literally, despite representing the same zero. -/
theorem all_zero_width_is_not_erased_by_the_front_end :
    value ([] : Bits) = value [false, false, false] ∧
      (next caller)^[107]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [false, false, false])) []) ctx)) =
        some (cfg (some dispatchLabel) (reset regs)
          { sourceTree := [0], targetTree := [0], fuel := [false, false, false] } ctx) ∧
      resultCfg (Λ := Λ) regs ctx (.success empty.val empty.val [] []) ≠
        resultCfg regs ctx (.success empty.val empty.val [false, false, false] []) := by
  refine ⟨rfl, run_code caller regs empty.val empty.val [false, false, false] [] ctx, ?_⟩
  intro same
  have lengths := congrArg (fun c : Cfg Γ Λ R => (c.stk (.inl .fuel)).length) same
  change 0 = 3 at lengths
  omega

/-- Literal little-endian bits, in nonpalindromic block order, reach the two actual destinations. -/
theorem explicit_bit_blocks_keep_endian_and_word_order :
    (next caller)^[6]
        (some (cfg (some (inputDecoderLabel .scan)) regs
          { inputBits := [true, true, false, false, false, false, true, true],
            certificateBits := [true, false, false] } ctx)) =
      some (cfg (some (InputParserMachine.treeLabel .source .init)) (afterInputDecoder regs)
        { inputRaw := [3, 12], certificateBits := [true, false, false] } ctx) ∧
    (next caller)^[6]
        (some (cfg (some (certificateDecoderLabel .scan)) regs
          { certificateBits := [true, true, false, false, false, false, true, true],
            sourceTree := [1, 0, 0], targetTree := [0], fuel := [true, false, false] } ctx)) =
      some (cfg (some dispatchLabel) (afterInputDecoder regs)
        { certificateWord := [3, 12], sourceTree := [1, 0, 0], targetTree := [0],
          fuel := [true, false, false] } ctx) :=
  ⟨dirty_input_decoding_runs_in_the_installed_global_program caller regs ctx
      { inputBits := [true, true, false, false, false, false, true, true],
        certificateBits := [true, false, false] },
    dirty_certificate_decoding_runs_in_the_installed_global_program caller regs ctx
      { certificateBits := [true, true, false, false, false, false, true, true],
        sourceTree := [1, 0, 0], targetTree := [0], fuel := [true, false, false] }⟩

/-- Removing the empty certificate-reverse premise changes both the time and returned bits. -/
theorem dirty_framing_scratch_cannot_be_dropped_from_the_entry_contract :
    (next caller)^[6]
        (some (cfg (some (framerLabel .scanPrefix)) regs
          { framedRaw := [true], frameCertReverse := [false, true] } ctx)) =
      some (cfg (some (inputDecoderLabel .scan)) (resetFramer regs)
        { certificateBits := [true, false] } ctx) ∧
      cfg (some (inputDecoderLabel (Λ := Λ) .scan)) (resetFramer regs)
        { certificateBits := [true, false] } ctx ≠
        cfg (some (inputDecoderLabel .scan)) (resetFramer regs) {} ctx := by
  refine ⟨dirty_framing_runs_in_the_installed_global_program caller regs ctx
    { framedRaw := [true], frameCertReverse := [false, true] }, ?_⟩
  intro same
  have bits := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .certificateBits)) same
  change [true, false] = [] at bits
  cases bits

/-- These two concrete partial-certificate words remain distinct even when their clocks agree. -/
theorem both_fixed_partial_certificate_orders_are_retained_on_input_failure :
    (next caller)^[14]
        (some (entry regs (frame [false] [true, false, false]) ctx)) =
      some (cfg (some rejectLabel) (afterInputDecoder regs)
        { certificateBits := [true, false, false] } ctx) ∧
      (next caller)^[17]
        (some (entry regs (frame [] [true, false, false]) ctx)) =
      some (cfg (some rejectLabel) (reset regs)
        { certificateBits := [true, false, false] } ctx) :=
  ⟨input_decode_failure_preserves_every_certificate_bit caller regs ctx [false] [true, false, false] rfl,
    input_parse_failure_restores_the_complete_word caller regs ctx [] [true, false, false] rfl⟩

/-- The failing routes expose the actual prior handoffs, including the last pre-certificate state. -/
theorem early_failure_routes_have_their_actual_intermediate_states :
    (next caller)^[12]
        (some (entry regs (frame [false] [false, true, true]) ctx)) =
      some (inputDecoderEntry regs [false] [false, true, true] ctx) ∧
      (next caller)^[10]
        (some (entry regs (frame [] [false, true, true]) ctx)) =
      some (inputDecoderEntry regs [] [false, true, true] ctx) ∧
      (next caller)^[12]
        (some (entry regs (frame [] [false, true, true]) ctx)) =
      some (inputEntry regs [] [false, true, true] ctx) ∧
      (next caller)^[50]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) [false, true, true]) ctx)) =
      some (inputDecoderEntry regs (wordBits (inputCode empty.val empty.val [])) [false, true, true] ctx) ∧
      (next caller)^[62]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) [false, true, true]) ctx)) =
      some (inputEntry regs (inputCode empty.val empty.val []) [false, true, true] ctx) ∧
      (next caller)^[75]
        (some (entry regs (frame (wordBits (inputCode empty.val empty.val [])) [false, true, true]) ctx)) =
      some (certificateDecoderEntry regs empty.val empty.val [] [false, true, true] ctx) := by
  have first := framing_returns_the_actual_two_fields caller regs ctx
    (wordBits (inputCode empty.val empty.val [])) [false, true, true]
  have second := the_input_decoder_returns_the_actual_word caller regs ctx
    (inputCode empty.val empty.val []) [false, true, true]
  have third := the_input_parser_returns_actual_fields caller regs ctx
    empty.val empty.val [] [false, true, true]
  exact ⟨(framing_returns_the_actual_two_fields caller regs ctx [false] [false, true, true]).run,
    (framing_returns_the_actual_two_fields caller regs ctx [] [false, true, true]).run,
    (Trace.trans caller (framing_returns_the_actual_two_fields caller regs ctx [] [false, true, true])
      (the_input_decoder_returns_the_actual_word caller regs ctx [] [false, true, true])).run,
    first.run, (Trace.trans caller first second).run,
    (Trace.trans caller (Trace.trans caller first second) third).run⟩

theorem actual_emitters_machine_time_and_source_verification_are_separate :
    emitPackedInputRun leftTwo.val rightTwo.val [true] =
        (wordBits (inputCode leftTwo.val rightTwo.val [true]), 112) ∧
      emitPackedCertificateRun [rootRight] = (wordBits [7, 10], 18) ∧
      (next caller)^[199]
        (some (entry regs (frame (emitPackedInputRun leftTwo.val rightTwo.val [true]).1
          (emitPackedCertificateRun [rootRight]).1) ctx)) =
        some (cfg (some dispatchLabel) (reset regs)
          { sourceTree := [1, 1, 0, 0, 0], targetTree := [1, 0, 1, 0, 0],
            fuel := [true], certificateWord := [7, 10] } ctx) ∧
      verifyBitsRun (emitPackedInputRun leftTwo.val rightTwo.val [true]).1
        (emitPackedCertificateRun [rootRight]).1 = (true, 137) := by
  refine ⟨emitPackedInputRun_eq leftTwo.val rightTwo.val [true], emitPackedCertificateRun_eq [rootRight],
    actual_packed_emitters_feed_the_composed_machine caller regs ctx
      leftTwo.val rightTwo.val [true] [rootRight], ?_⟩
  rw [emitPackedInputRun_value, emitPackedCertificateRun_value]
  exact Examples.RotationCertificateBinary.packed_one_rotation

end FinalSeparators

end Examples.RotationCertificateFrontEndMachine
