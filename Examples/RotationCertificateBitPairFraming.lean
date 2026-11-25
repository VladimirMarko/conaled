import Applications.Resources.RotationCertificate.BitPairFraming
import Examples.RotationCertificateBinary

/-!
# Connected strict binary pair framing

Guard positions distinguish a true payload from the delimiter. Every subsequent
bit belongs to the certificate, with both coordinate orders and widths retained.
The actual machine clients include malformed-prefix cleanup, arbitrary phase
accumulators and output suffixes, reset registers, present halted results, and
the sharp extra workspace cell. Packed emitters feed the source framing and
verification composition. Its Boolean and source-event observations remain
separate from the actual framing-machine transitions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateBitPairFraming
open Trees Trees.Rotations Resources
open Resources.BinaryCounter (Bits value)
open Resources.RotationCertificate
open Resources.RotationCertificate.BitPairFraming
open RotationDistanceExample (leftTwo rightTwo rootRight)

/-! Exact raw recognition preserves both coordinates and their boundary. -/

theorem frame_equality_recovers_both_coordinates (input cert otherInput otherCert : Bits) :
    frame input cert = frame otherInput otherCert ↔
      input = otherInput ∧ cert = otherCert := by
  constructor
  · intro equal
    have pairs : (input, cert) = (otherInput, otherCert) := frame_injective equal
    exact ⟨congrArg Prod.fst pairs, congrArg Prod.snd pairs⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem result_codes_recover_the_complete_result (left right : Option (Bits × Bits)) :
    resultCode left = resultCode right ↔ left = right :=
  ⟨fun equal => resultCode_injective equal, congrArg resultCode⟩

theorem failure_and_empty_pair_have_distinct_codes :
    resultCode none = [] ∧ resultCode (some ([], [])) = [none, none] ∧
      resultCode none ≠ resultCode (some ([], [])) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  cases resultCode_injective equal

theorem the_output_separator_preserves_coordinate_order :
    resultCode (some ([false], [])) ≠ resultCode (some ([], [false])) ∧
      frame [false] [] ≠ frame [] [false] := by
  constructor
  · intro equal
    exact (by decide : (some (([false], []) : Bits × Bits)) ≠ some ([], [false]))
      (resultCode_injective equal)
  · intro equal
    exact (by decide : (([false], []) : Bits × Bits) ≠ ([], [false]))
      (frame_injective equal)

theorem raw_success_recovers_every_original_bit (raw input cert : Bits)
    (parsed : unframe raw = some (input, cert)) :
    raw = frame input cert ∧ raw.length = 2 * input.length + cert.length + 1 ∧
      next^[2 * input.length + 2 * cert.length + 4]
        (some (Turing.initList machine raw)) =
        some (Turing.haltList machine (resultCode (some (input, cert)))) := by
  have encoded := (unframe_iff raw input cert).1 parsed
  subst raw
  exact ⟨rfl, frame_length input cert, machine_run_frame input cert⟩

theorem every_malformed_prefix_is_rejected_and_cleared (input : Bits) :
    unframe (escapeBits input) = none ∧
      unframe (escapeBits input ++ [false]) = none ∧
      next^[2 * input.length + 2]
        (some (Turing.initList machine (escapeBits input))) =
        some (Turing.haltList machine []) ∧
      next^[2 * input.length + 2]
        (some (Turing.initList machine (escapeBits input ++ [false]))) =
        some (Turing.haltList machine []) :=
  ⟨unframe_missing_delimiter input, unframe_incomplete_guard input,
    machine_run_missing_delimiter input, machine_run_incomplete_guard input⟩

theorem arbitrary_raw_failure_has_a_missing_delimiter (raw : Bits)
    (failed : unframe raw = none) :
    ∃ input : Bits, raw = escapeBits input ∨ raw = escapeBits input ++ [false] :=
  (unframe_none_iff raw).1 failed

theorem an_escaped_prefix_cannot_repair_a_failed_suffix (pref raw : Bits)
    (failed : unframe raw = none) : unframe (escapeBits pref ++ raw) = none := by
  rw [unframe_escape_append, failed]
  rfl

/-! Literal EOF, guard and flag positions have different meanings. -/

theorem eof_and_a_lone_false_guard_reject :
    unframe [] = none ∧ unframe [false] = none ∧
      next^[2] (some (Turing.initList machine [])) =
        some (Turing.haltList machine []) ∧
      next^[2] (some (Turing.initList machine [false])) =
        some (Turing.haltList machine []) :=
  ⟨unframe_nil, unframe_false_nil,
    machine_run_missing_delimiter [], machine_run_incomplete_guard []⟩

theorem a_guarded_payload_still_requires_its_delimiter (bit : Bool) :
    unframe [false, bit] = none ∧
      unframe [false, bit, false] = none ∧
      unframe [false, bit, true] = some ([bit], []) ∧
      next^[4] (some (Turing.initList machine [false, bit])) =
        some (Turing.haltList machine []) ∧
      next^[4] (some (Turing.initList machine [false, bit, false])) =
        some (Turing.haltList machine []) ∧
      next^[6] (some (Turing.initList machine [false, bit, true])) =
        some (Turing.haltList machine [none, some bit, none]) :=
  ⟨unframe_missing_delimiter [bit], unframe_incomplete_guard [bit],
    unframe_frame [bit] [], machine_run_missing_delimiter [bit],
    machine_run_incomplete_guard [bit], machine_run_frame [bit] []⟩

theorem a_true_flag_retains_every_certificate_bit (cert : Bits) :
    unframe (true :: cert) = some ([], cert) ∧
      next^[2 * cert.length + 4] (some (Turing.initList machine (true :: cert))) =
        some (Turing.haltList machine (none :: none :: cert.map some)) := by
  refine ⟨unframe_frame [] cert, ?_⟩
  have run := machine_run_frame [] cert
  change next^[0 + 2 * cert.length + 4]
    (some (Turing.initList machine (true :: cert))) =
      some (Turing.haltList machine (none :: none :: cert.map some)) at run
  rw [Nat.zero_add] at run
  exact run

theorem opposite_coordinates_produce_opposite_outputs :
    next^[8] (some (Turing.initList machine [false, true, true, false])) =
        some (Turing.haltList machine [none, some true, none, some false]) ∧
      next^[8] (some (Turing.initList machine [false, false, true, true])) =
        some (Turing.haltList machine [none, some false, none, some true]) :=
  ⟨machine_run_frame [true] [false], machine_run_frame [false] [true]⟩

theorem nonpalindromic_coordinates_keep_their_order :
    unframe [false, true, false, false, true, true, false, false] =
        some ([true, false], [true, false, false]) ∧
      next^[14] (some (Turing.initList machine
        [false, true, false, false, true, true, false, false])) =
        some (Turing.haltList machine
          [none, some true, some false, none, some true, some false, some false]) :=
  ⟨unframe_frame [true, false] [true, false, false],
    machine_run_frame [true, false] [true, false, false]⟩

theorem appending_extends_exactly_the_certificate (input cert tail : Bits) :
    unframe (frame input cert ++ tail) = some (input, cert ++ tail) ∧
      next^[2 * input.length + 2 * (cert ++ tail).length + 4]
        (some (Turing.initList machine (frame input cert ++ tail))) =
        some (Turing.haltList machine (resultCode (some (input, cert ++ tail)))) := by
  rw [frame_append]
  exact ⟨unframe_frame input (cert ++ tail), machine_run_frame input (cert ++ tail)⟩

theorem valid_frames_can_be_strict_prefixes_of_other_valid_frames :
    frame [] [] ++ [false] = frame [] [false] ∧
      frame [] [] ≠ frame [] [false] ∧
      unframe (frame [] []) = some ([], []) ∧
      unframe (frame [] [false]) = some ([], [false]) :=
  ⟨frame_append [] [] [false], by decide,
    unframe_frame [] [], unframe_frame [] [false]⟩

theorem zero_width_in_either_coordinate_is_observable :
    value ([] : Bits) = value [false] ∧
      frame [] [] ≠ frame [false] [] ∧
      value (frame [] []) = value (frame [] [false]) ∧
      next^[4] (some (Turing.initList machine (frame [] []))) =
        some (Turing.haltList machine [none, none]) ∧
      next^[6] (some (Turing.initList machine (frame [] [false]))) =
        some (Turing.haltList machine [none, none, some false]) :=
  ⟨rfl, by decide, rfl, machine_run_frame [] [], machine_run_frame [] [false]⟩

/-! Actual state transitions include resets and clearing of accumulated payloads. -/

theorem initialization_contains_no_precomputed_pair (raw : Bits) :
    (Turing.initList machine raw).var = zeroRegisters ∧
      (Turing.initList machine raw).stk .input = raw ∧
      (Turing.initList machine raw).stk .firstReverse = [] ∧
      (Turing.initList machine raw).stk .certReverse = [] ∧
      (Turing.initList machine raw).stk .output = [] := by
  rw [initList_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stale_registers_cannot_supply_a_missing_flag_or_value
    (firstRev certRev : Bits) (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .scanPrefix) regs [] firstRev certRev out) =
        some (cfg (some .clearFirst) zeroRegisters [] firstRev certRev out) ∧
      machine.step (cfg (some .scanPrefix) regs [false] firstRev certRev out) =
        some (cfg (some .clearFirst) zeroRegisters [] firstRev certRev out) :=
  ⟨scanPrefix_step_nil firstRev certRev out regs,
    scanPrefix_step_false_nil firstRev certRev out regs⟩

theorem stale_registers_do_not_confuse_true_payload_and_delimiter
    (raw firstRev certRev : Bits) (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .scanPrefix) regs (false :: true :: raw)
        firstRev certRev out) =
        some (cfg (some .scanPrefix) zeroRegisters raw (true :: firstRev) certRev out) ∧
      machine.step (cfg (some .scanPrefix) regs (true :: raw) firstRev certRev out) =
        some (cfg (some .copyCert) zeroRegisters raw firstRev certRev out) :=
  ⟨scanPrefix_step_false_cons true raw firstRev certRev out regs,
    scanPrefix_step_true raw firstRev certRev out regs⟩

theorem escaped_true_failure_has_four_visible_transitions :
    machine.step (Turing.initList machine [false, true]) =
        some (cfg (some .scanPrefix) zeroRegisters [] [true] [] []) ∧
      machine.step (cfg (some .scanPrefix) zeroRegisters [] [true] [] []) =
        some (cfg (some .clearFirst) zeroRegisters [] [true] [] []) ∧
      machine.step (cfg (some .clearFirst) zeroRegisters [] [true] [] []) =
        some (cfg (some .clearFirst) zeroRegisters [] [] [] []) ∧
      machine.step (cfg (some .clearFirst) zeroRegisters [] [] [] []) =
        some (Turing.haltList machine []) := by
  refine ⟨?_, scanPrefix_step_nil [true] [] [] zeroRegisters,
    clearFirst_step_cons true [] [] [] [] zeroRegisters, ?_⟩
  · rw [initList_eq]
    exact scanPrefix_step_false_cons true [] [] [] [] zeroRegisters
  · rw [haltList_eq]
    exact clearFirst_step_nil [] [] [] zeroRegisters

/-! General phase clients use precisely the stacks that their contracts permit. -/

theorem accumulated_first_bits_precede_the_new_pair
    (input cert firstRev : Bits) (out : List (Option Bool)) (regs : Registers) :
    next^[2 * input.length + 2 * cert.length + 4 + firstRev.length]
        (some (cfg (some .scanPrefix) regs (frame input cert) firstRev [] out)) =
      some (Turing.haltList machine
        (resultCode (some (firstRev.reverse ++ input, cert)) ++ out)) := by
  have run := scanPrefix_iterate (frame input cert) firstRev out regs
  rw [runSteps_frame, unframe_frame] at run
  exact run

theorem a_failed_suffix_clears_old_first_bits_and_preserves_old_output
    (raw firstRev : Bits) (out : List (Option Bool)) (regs : Registers)
    (failed : unframe raw = none) :
    next^[runSteps raw + firstRev.length]
        (some (cfg (some .scanPrefix) regs raw firstRev [] out)) =
      some (Turing.haltList machine out) := by
  have run := scanPrefix_iterate raw firstRev out regs
  rw [failed] at run
  exact run

theorem emitting_first_bits_preserves_an_arbitrary_output_suffix
    (out : List (Option Bool)) (regs : Registers) :
    next^[3] (some (cfg (some .emitFirst) regs [] [false, true] [] out)) =
      some (Turing.haltList machine (none :: some true :: some false :: out)) :=
  emitFirst_iterate [false, true] out regs

theorem emitting_both_coordinates_preserves_an_arbitrary_output_suffix
    (out : List (Option Bool)) (regs : Registers) :
    next^[7] (some (cfg (some .emitCert) regs []
      [false, true] [false, false, true] out)) =
      some (Turing.haltList machine
        (none :: some true :: some false :: none ::
          some true :: some false :: some false :: out)) :=
  emitCert_iterate [false, true] [false, false, true] out regs

theorem copying_retains_old_certificate_bits_before_the_raw_suffix
    (raw : Bits) (out : List (Option Bool)) (regs : Registers) :
    next^[2 * raw.length + 7]
        (some (cfg (some .copyCert) regs raw [false, true] [true, false] out)) =
      some (Turing.haltList machine
        (none :: some true :: some false :: none ::
          some false :: some true :: (raw.map some ++ out))) := by
  have count : 2 * raw.length + ([true, false] : Bits).length +
      ([false, true] : Bits).length + 3 = 2 * raw.length + 7 := by
    simp only [List.length_cons, List.length_nil]
  have run := copyCert_iterate raw [false, true] [true, false] out regs
  rw [count] at run
  exact run

theorem clearing_preserves_an_arbitrary_output_suffix
    (out : List (Option Bool)) (regs : Registers) :
    next^[3] (some (cfg (some .clearFirst) regs [] [true, false] [] out)) =
      some (Turing.haltList machine out) :=
  clearFirst_iterate [true, false] out regs

theorem clearing_does_not_erase_an_unrelated_certificate_stack
    (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .clearFirst) regs [] [] [true] out) =
        some (cfg none zeroRegisters [] [] [true] out) ∧
      cfg none zeroRegisters [] [] [true] out ≠ Turing.haltList machine out := by
  refine ⟨clearFirst_step_nil [] [true] out regs, ?_⟩
  intro equal
  have impossible := congrArg (fun c : machine.Cfg => c.stk .certReverse) equal
  rw [haltList_eq] at impossible
  cases impossible

theorem every_work_alphabet_is_finite (stack : StackId) :
    Finite (machine.Γ stack) := by
  change Finite (alphabet stack)
  infer_instance

/-! A real four-step path attains the extra-cell workspace bound. -/

theorem the_empty_pair_has_four_visible_transitions :
    machine.step (Turing.initList machine [true]) =
        some (cfg (some .copyCert) zeroRegisters [] [] [] []) ∧
      machine.step (cfg (some .copyCert) zeroRegisters [] [] [] []) =
        some (cfg (some .emitCert) zeroRegisters [] [] [] []) ∧
      machine.step (cfg (some .emitCert) zeroRegisters [] [] [] []) =
        some (cfg (some .emitFirst) zeroRegisters [] [] [] [none]) ∧
      machine.step (cfg (some .emitFirst) zeroRegisters [] [] [] [none]) =
        some (Turing.haltList machine [none, none]) := by
  refine ⟨?_, copyCert_step_nil [] [] [] zeroRegisters,
    emitCert_step_nil [] [] [] zeroRegisters, ?_⟩
  · rw [initList_eq]
    exact scanPrefix_step_true [] [] [] [] zeroRegisters
  · rw [haltList_eq]
    exact emitFirst_step_nil [] [] [none] zeroRegisters

theorem the_empty_pair_requires_the_extra_workspace_cell :
    Turing.TM2.Reaches program (Turing.initList machine [true])
        (Turing.haltList machine [none, none]) ∧
      stackCells (Turing.haltList machine [none, none]) = 2 ∧
      stackCells (Turing.haltList machine [none, none]) ≤ ([true] : Bits).length + 1 ∧
      ¬ stackCells (Turing.haltList machine [none, none]) ≤ ([true] : Bits).length := by
  have steps := the_empty_pair_has_four_visible_transitions
  have reached : Turing.TM2.Reaches program (Turing.initList machine [true])
      (Turing.haltList machine [none, none]) := by
    change Relation.ReflTransGen
      (fun before after : machine.Cfg => machine.step before = some after) _ _
    refine Relation.ReflTransGen.head
      (b := cfg (some .copyCert) zeroRegisters [] [] [] []) ?_ ?_
    · exact steps.1
    · refine Relation.ReflTransGen.head
        (b := cfg (some .emitCert) zeroRegisters [] [] [] []) ?_ ?_
      · exact steps.2.1
      · refine Relation.ReflTransGen.head
          (b := cfg (some .emitFirst) zeroRegisters [] [] [] [none]) ?_ ?_
        · exact steps.2.2.1
        · exact Relation.ReflTransGen.single steps.2.2.2
  have cells : stackCells (Turing.haltList machine [none, none]) = 2 := by
    rw [haltList_eq]
    rfl
  refine ⟨reached, cells,
    reachable_stackCells_le [true] (Turing.haltList machine [none, none]) reached, ?_⟩
  rw [cells]
  decide

theorem every_reachable_stack_obeys_the_uniform_space_bound
    (raw : Bits) (reached : machine.Cfg)
    (run : Turing.TM2.Reaches program (Turing.initList machine raw) reached) :
    (reached.stk .input).length ≤ raw.length + 1 ∧
      (reached.stk .firstReverse).length ≤ raw.length + 1 ∧
      (reached.stk .certReverse).length ≤ raw.length + 1 ∧
      (reached.stk .output).length ≤ raw.length + 1 := by
  have bounded := reachable_stackCells_le raw reached run
  unfold stackCells at bounded
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! Outer absence follows a halt and erases the distinction between its outputs. -/

theorem a_step_past_the_halted_result_returns_outer_none (raw : Bits) :
    next^[runSteps raw + 1] (some (Turing.initList machine raw)) = none := by
  rw [Function.iterate_succ_apply', machine_run]
  rfl

theorem failure_and_empty_success_are_present_before_outer_none :
    next^[2] (some (Turing.initList machine [])) =
        some (Turing.haltList machine []) ∧
      next^[3] (some (Turing.initList machine [])) = none ∧
      next^[4] (some (Turing.initList machine [true])) =
        some (Turing.haltList machine [none, none]) ∧
      next^[5] (some (Turing.initList machine [true])) = none :=
  ⟨machine_run_missing_delimiter [], a_step_past_the_halted_result_returns_outer_none [],
    machine_run_frame [] [], a_step_past_the_halted_result_returns_outer_none [true]⟩

theorem certificate_only_frames_attain_the_linear_transition_bound (cert : Bits) :
    next^[2 * (true :: cert).length + 2]
        (some (Turing.initList machine (true :: cert))) =
      some (Turing.haltList machine (none :: none :: cert.map some)) := by
  have count : 2 * (true :: cert).length + 2 = 2 * cert.length + 4 := by
    simp only [List.length_cons]
    omega
  rw [count]
  exact (a_true_flag_retains_every_certificate_bit cert).2

theorem every_raw_input_has_an_actual_linear_run (raw : Bits) :
    ∃ steps, steps ≤ 2 * raw.length + 2 ∧
      next^[steps] (some (Turing.initList machine raw)) =
        some (Turing.haltList machine (resultCode (unframe raw))) := by
  let evidence := outputsInTime raw
  exact ⟨evidence.steps, evidence.steps_le_m, evidence.evals_in_steps⟩

theorem every_raw_input_uses_one_polynomial_machine (raw : Bits) :
    ∃ steps, steps ≤ computableInPolyTime.time.eval raw.length ∧
      (fun c : Option computableInPolyTime.tm.Cfg =>
        c.bind computableInPolyTime.tm.step)^[steps]
        (some (Turing.initList computableInPolyTime.tm
          (raw.map computableInPolyTime.inputAlphabet.invFun))) =
        some (Turing.haltList computableInPolyTime.tm
          ((resultCode (unframe raw)).map computableInPolyTime.outputAlphabet.invFun)) := by
  let evidence := computableInPolyTime.outputsFun raw
  exact ⟨evidence.steps, evidence.steps_le_m, evidence.evals_in_steps⟩

noncomputable def framedPairOutputsInTime (input cert : Bits) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((frame input cert).map computableInPolyTime.inputAlphabet.invFun)
      (some ((resultCode (some (input, cert))).map
        computableInPolyTime.outputAlphabet.invFun))
      (computableInPolyTime.time.eval (2 * input.length + cert.length + 1)) := by
  have evidence := computableInPolyTime.outputsFun (frame input cert)
  simpa only [id_eq, unframe_frame, frame_length] using evidence

/-! Actual decoded fields feed the unchanged binary verifier. -/

theorem returned_fields_feed_the_existing_verifier (raw input cert : Bits)
    (parsed : unframe raw = some (input, cert)) :
    verifyFramed raw = (verifyBitsRun input cert).1 := by
  rw [(unframe_iff raw input cert).1 parsed, verifyFramed_frame]

theorem an_empty_first_coordinate_is_valid_framing_but_fails_verification (cert : Bits) :
    unframe (true :: cert) = some ([], cert) ∧ verifyFramed (true :: cert) = false := by
  refine ⟨unframe_frame [] cert, ?_⟩
  have checked := verifyFramed_frame [] cert
  rw [Examples.RotationCertificateBinary.decoded_empty_input_skips_the_certificate cert]
    at checked
  exact checked

theorem actual_packed_emitters_feed_framing_decoding_and_acceptance
    (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove)
    (run : applyMoves? moves source = some target) (bounded : moves.length ≤ value bs) :
    unframe (frame (emitPackedInputRun source target bs).1
        (emitPackedCertificateRun moves).1) =
        some ((emitPackedInputRun source target bs).1, (emitPackedCertificateRun moves).1) ∧
      verifyFramed (frame (emitPackedInputRun source target bs).1
        (emitPackedCertificateRun moves).1) = true ∧
      next^[2 * (emitPackedInputRun source target bs).1.length +
          2 * (emitPackedCertificateRun moves).1.length + 4]
        (some (Turing.initList machine (frame (emitPackedInputRun source target bs).1
          (emitPackedCertificateRun moves).1))) =
        some (Turing.haltList machine (resultCode
          (some ((emitPackedInputRun source target bs).1,
            (emitPackedCertificateRun moves).1)))) :=
  ⟨unframe_frame _ _, verifyFramed_emit_trace source target bs moves run bounded,
    machine_run_frame _ _⟩

def oneRotationInput : Bits := (emitPackedInputRun leftTwo.val rightTwo.val [true]).1

def oneRotationCertificate : Bits := (emitPackedCertificateRun [rootRight]).1

theorem one_rotation_emitter_values :
    oneRotationInput = wordBits (inputCode leftTwo.val rightTwo.val [true]) ∧
      oneRotationCertificate = wordBits (certCode [rootRight]) :=
  ⟨emitPackedInputRun_value leftTwo.val rightTwo.val [true],
    emitPackedCertificateRun_value [rootRight]⟩

theorem one_rotation_coordinate_lengths :
    oneRotationInput.length = 56 ∧ oneRotationCertificate.length = 8 := by
  rw [one_rotation_emitter_values.1, one_rotation_emitter_values.2]
  exact ⟨Examples.RotationCertificateBinary.one_rotation_bit_lengths.1,
    Examples.RotationCertificateBinary.one_rotation_bit_lengths.2.1⟩

theorem one_rotation_verifier_observation :
    verifyBitsRun oneRotationInput oneRotationCertificate = (true, 137) := by
  rw [one_rotation_emitter_values.1, one_rotation_emitter_values.2]
  exact Examples.RotationCertificateBinary.packed_one_rotation

theorem one_rotation_framing_has_the_expected_size_time_and_output :
    (frame oneRotationInput oneRotationCertificate).length = 121 ∧
      (resultCode (some (oneRotationInput, oneRotationCertificate))).length = 66 ∧
      runSteps (frame oneRotationInput oneRotationCertificate) = 132 ∧
      next^[132] (some (Turing.initList machine
        (frame oneRotationInput oneRotationCertificate))) =
        some (Turing.haltList machine
          (resultCode (some (oneRotationInput, oneRotationCertificate)))) ∧
      verifyFramed (frame oneRotationInput oneRotationCertificate) = true := by
  obtain ⟨inputLength, certLength⟩ := one_rotation_coordinate_lengths
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [frame_length, inputLength, certLength]
  · rw [resultCode_length, inputLength, certLength]
  · rw [runSteps_frame, inputLength, certLength]
  · have run := machine_run_frame oneRotationInput oneRotationCertificate
    rw [inputLength, certLength] at run
    exact run
  · rw [verifyFramed_frame, one_rotation_verifier_observation]

theorem an_appended_certificate_bit_remains_framed_but_fails_the_verifier (bit : Bool) :
    unframe (frame oneRotationInput (oneRotationCertificate ++ [bit])) =
        some (oneRotationInput, oneRotationCertificate ++ [bit]) ∧
      (frame oneRotationInput (oneRotationCertificate ++ [bit])).length = 122 ∧
      runSteps (frame oneRotationInput (oneRotationCertificate ++ [bit])) = 134 ∧
      next^[134] (some (Turing.initList machine
        (frame oneRotationInput (oneRotationCertificate ++ [bit])))) =
        some (Turing.haltList machine
          (resultCode (some (oneRotationInput, oneRotationCertificate ++ [bit])))) ∧
      verifyBitsRun oneRotationInput (oneRotationCertificate ++ [bit]) = (false, 112) ∧
      verifyFramed (frame oneRotationInput (oneRotationCertificate ++ [bit])) = false := by
  obtain ⟨inputLength, certLength⟩ := one_rotation_coordinate_lengths
  have extendedLength : (oneRotationCertificate ++ [bit]).length = 9 := by
    rw [List.length_append, certLength]
    rfl
  have checked : verifyBitsRun oneRotationInput (oneRotationCertificate ++ [bit]) =
      (false, 112) := by
    rw [one_rotation_emitter_values.1, one_rotation_emitter_values.2]
    exact Examples.RotationCertificateBinary.valid_move_bits_then_partial_block bit
  refine ⟨unframe_frame _ _, ?_, ?_, ?_, checked, ?_⟩
  · rw [frame_length, inputLength, extendedLength]
  · rw [runSteps_frame, inputLength, extendedLength]
  · have run := machine_run_frame oneRotationInput (oneRotationCertificate ++ [bit])
    rw [inputLength, extendedLength] at run
    exact run
  · rw [verifyFramed_frame, checked]

/-! One chosen witness carries acceptance and both actual framing resource bounds. -/

theorem binary_source_work_is_bounded_by_the_framed_length (input cert : Bits) :
    (verifyBitsRun input cert).2 ≤ 40 * (frame input cert).length ^ 2 := by
  have work := verifyBitsRun_work_all input cert
  have size : input.length + cert.length + 1 ≤ (frame input cert).length := by
    rw [frame_length]
    omega
  have squares := Nat.mul_le_mul size size
  simp only [pow_two] at work ⊢
  nlinarith

theorem a_single_small_witness_has_acceptance_time_and_space
    (input : Bits) (yes : BinaryYes input) :
    ∃ cert : Bits, cert.length ≤ input.length ^ 2 ∧
      (frame input cert).length ≤ (input.length + 1) ^ 2 ∧
      verifyFramed (frame input cert) = true ∧
      Nonempty (Turing.TM2OutputsInTime machine (frame input cert)
        (some (resultCode (some (input, cert)))) (2 * (input.length + 1) ^ 2 + 2)) ∧
      ∀ reached : machine.Cfg,
        Turing.TM2.Reaches program (Turing.initList machine (frame input cert)) reached →
          stackCells reached ≤ (input.length + 1) ^ 2 + 1 := by
  obtain ⟨cert, small, frameSmall, accepted⟩ := verifyFramed_complete_small input yes
  refine ⟨cert, small, frameSmall, accepted, ⟨outputsInTimeOfSmallCertificate input cert small⟩, ?_⟩
  intro reached run
  exact reachable_framed_stackCells_le input cert small reached run

theorem the_one_rotation_witness_client_is_nonvacuous : BinaryYes oneRotationInput := by
  rw [one_rotation_emitter_values.1]
  exact Examples.RotationCertificateBinary.one_rotation_binary_language_is_inhabited

end Examples.RotationCertificateBitPairFraming
