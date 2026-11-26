import Applications.Resources.RotationCertificate.BitDecoderMachine

/-!
# Connected finite-control decoder runs

These clients retain complete raw-input decoding, marked empty success, ordinary
rejection as an actual halted output, and cleanup of every decoded prefix.
Literal cases distinguish endian order, block order and fixed zero width.
The transition counts belong to the actual TM2 program; source-event work is
a separate observation. The polynomial-time client uses the constructed
machine record and its explicit result encoding.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateBitDecoderMachine
open Resources.BinaryCounter (Bits value)
open Resources.RotationCertificate
open Resources.RotationCertificate.BitDecoderMachine

/-! The output alphabet distinguishes all source results, including empty success. -/

theorem encoded_results_are_equal_exactly_when_results_are_equal
    (left right : Option Word) :
    resultCode left = resultCode right ↔ left = right :=
  ⟨fun equal => resultCode_injective equal, congrArg resultCode⟩

theorem rejection_and_empty_success_have_distinct_codes :
    resultCode none = [] ∧ resultCode (some []) = [none] ∧
      resultCode none ≠ resultCode (some []) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  cases resultCode_injective equal

theorem empty_input_halts_with_the_success_marker :
    next^[2] (some (Turing.initList machine [])) =
      some (Turing.haltList machine [none]) :=
  machine_run_code []

theorem every_short_input_halts_with_rejection (a b c : Bool) :
    next^[2] (some (Turing.initList machine [a])) =
        some (Turing.haltList machine []) ∧
      next^[2] (some (Turing.initList machine [a, b])) =
        some (Turing.haltList machine []) ∧
      next^[2] (some (Turing.initList machine [a, b, c])) =
        some (Turing.haltList machine []) :=
  ⟨machine_run_partial [] [a] (by simp) (by simp),
    machine_run_partial [] [a, b] (by simp) (by simp),
    machine_run_partial [] [a, b, c] (by simp) (by simp)⟩

/-! Every complete four-bit block is data, with the literal low bit first. -/

theorem every_four_bit_block_reaches_its_payload (b0 b1 b2 b3 : Bool) :
    next^[4] (some (Turing.initList machine [b0, b1, b2, b3])) =
      some (Turing.haltList machine [none, some (decodeTagRun b0 b1 b2 b3).1]) := by
  have run := machine_run_code [(decodeTagRun b0 b1 b2 b3).1]
  simpa only [wordBits, List.append_nil, tagBits_decodeTagRun, resultCode,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil] using run

theorem literal_endian_blocks :
    next^[4] (some (Turing.initList machine [true, false, false, false])) =
        some (Turing.haltList machine [none, some (1 : Tag)]) ∧
      next^[4] (some (Turing.initList machine [false, false, false, true])) =
        some (Turing.haltList machine [none, some (8 : Tag)]) :=
  ⟨machine_run_code [1], machine_run_code [8]⟩

theorem literal_zero_and_reserved_blocks :
    next^[4] (some (Turing.initList machine [false, false, false, false])) =
        some (Turing.haltList machine [none, some (0 : Tag)]) ∧
      next^[4] (some (Turing.initList machine [true, true, true, true])) =
        some (Turing.haltList machine [none, some (15 : Tag)]) :=
  ⟨machine_run_code [0], machine_run_code [15]⟩

theorem reserved_tags_survive_in_order :
    next^[12] (some (Turing.initList machine (wordBits [11, 12, 13, 14, 15]))) =
      some (Turing.haltList machine
        [none, some (11 : Tag), some 12, some 13, some 14, some 15]) :=
  machine_run_code [11, 12, 13, 14, 15]

theorem two_literal_blocks_keep_their_order :
    next^[6] (some (Turing.initList machine
      [true, false, false, false, false, false, false, true])) =
      some (Turing.haltList machine [none, some (1 : Tag), some 8]) :=
  machine_run_code [1, 8]

theorem three_nonpalindromic_blocks_keep_their_order :
    next^[8] (some (Turing.initList machine
      [false, false, false, false, true, true, true, true, true, false, false, false])) =
      some (Turing.haltList machine [none, some (0 : Tag), some 15, some 1]) :=
  machine_run_code [0, 15, 1]

/-! Equal numeric values do not permit erasing encoded blocks. -/

theorem a_zero_block_is_not_an_empty_word :
    value (wordBits []) = value (wordBits [0]) ∧
      resultCode (some []) ≠ resultCode (some [0]) ∧
      next^[2] (some (Turing.initList machine (wordBits []))) =
        some (Turing.haltList machine [none]) ∧
      next^[4] (some (Turing.initList machine (wordBits [0]))) =
        some (Turing.haltList machine [none, some (0 : Tag)]) := by
  refine ⟨rfl, ?_, machine_run_code [], machine_run_code [0]⟩
  intro equal
  exact (by decide : (some ([] : Word)) ≠ some [0]) (resultCode_injective equal)

theorem high_zero_blocks_retain_their_width :
    value (wordBits [1]) = value (wordBits [1, 0]) ∧
      resultCode (some [1]) ≠ resultCode (some [1, 0]) ∧
      next^[4] (some (Turing.initList machine (wordBits [1]))) =
        some (Turing.haltList machine [none, some (1 : Tag)]) ∧
      next^[6] (some (Turing.initList machine (wordBits [1, 0]))) =
        some (Turing.haltList machine [none, some (1 : Tag), some 0]) := by
  refine ⟨rfl, ?_, machine_run_code [1], machine_run_code [1, 0]⟩
  intro equal
  exact (by decide : (some ([1] : Word)) ≠ some [1, 0]) (resultCode_injective equal)

theorem two_zero_blocks_both_survive :
    next^[6] (some (Turing.initList machine
      [false, false, false, false, false, false, false, false])) =
      some (Turing.haltList machine [none, some (0 : Tag), some 0]) :=
  machine_run_code [0, 0]

/-! The exact halted target includes empty auxiliary stacks and reset finite state. -/

theorem every_partial_ending_clears_the_whole_prefix (pref : Word) (a b c : Bool) :
    next^[2 * pref.length + 2]
        (some (Turing.initList machine (wordBits pref ++ [a]))) =
        some (Turing.haltList machine []) ∧
      next^[2 * pref.length + 2]
        (some (Turing.initList machine (wordBits pref ++ [a, b]))) =
        some (Turing.haltList machine []) ∧
      next^[2 * pref.length + 2]
        (some (Turing.initList machine (wordBits pref ++ [a, b, c]))) =
        some (Turing.haltList machine []) :=
  ⟨machine_run_partial pref [a] (by simp) (by simp),
    machine_run_partial pref [a, b] (by simp) (by simp),
    machine_run_partial pref [a, b, c] (by simp) (by simp)⟩

theorem one_and_two_completed_blocks_are_cleared (bit : Bool) :
    next^[4] (some (Turing.initList machine (wordBits [1] ++ [bit]))) =
        some (Turing.haltList machine []) ∧
      next^[6] (some (Turing.initList machine (wordBits [15, 1] ++ [bit]))) =
        some (Turing.haltList machine []) :=
  ⟨machine_run_partial [1] [bit] (by simp) (by simp),
    machine_run_partial [15, 1] [bit] (by simp) (by simp)⟩

theorem initialization_carries_no_precomputed_answer (raw : Bits) :
    (Turing.initList machine raw).var = zeroRegisters ∧
      (Turing.initList machine raw).stk .input = raw ∧
      (Turing.initList machine raw).stk .reverse = [] ∧
      (Turing.initList machine raw).stk .output = [] := by
  rw [initList_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem one_tag_failure_has_four_visible_transitions (bit : Bool) :
    machine.step (Turing.initList machine [false, false, false, false, bit]) =
        some (cfg (some .scan) zeroRegisters [bit] [0] []) ∧
      machine.step (cfg (some .scan) zeroRegisters [bit] [0] []) =
        some (cfg (some .clear) zeroRegisters [] [0] []) ∧
      machine.step (cfg (some .clear) zeroRegisters [] [0] []) =
        some (cfg (some .clear) zeroRegisters [] [] []) ∧
      machine.step (cfg (some .clear) zeroRegisters [] [] []) =
        some (Turing.haltList machine []) := by
  refine ⟨?_, scan_step_one bit [0] [] zeroRegisters,
    clear_step_cons 0 [] [] [] zeroRegisters, ?_⟩
  · rw [initList_eq]
    exact scan_step_block false false false false [bit] [] [] zeroRegisters
  · rw [haltList_eq]
    exact clear_step_nil [] [] zeroRegisters

theorem stale_registers_do_not_change_the_next_complete_block
    (regs : Registers) (raw : Bits) (rev : Word) (out : List (Option Tag)) :
    machine.step
        (cfg (some .scan) regs (true :: false :: false :: false :: raw) rev out) =
      some (cfg (some .scan) zeroRegisters raw (1 :: rev) out) :=
  scan_step_block true false false false raw rev out regs

/-! Phase clients retain the open accumulators introduced by actual execution. -/

theorem already_accumulated_tags_precede_a_decoded_suffix
    (rev suffix : Word) (regs : Registers) :
    next^[2 * suffix.length + rev.length + 2]
        (some (cfg (some .scan) regs (wordBits suffix) rev [])) =
      some (Turing.haltList machine (none :: (rev.reverse ++ suffix).map some)) := by
  have count : 2 * ((wordBits suffix).length / 4) + rev.length + 2 =
      2 * suffix.length + rev.length + 2 := by
    rw [wordBits_length]
    omega
  have run := scan_iterate (wordBits suffix) rev regs
  rw [count, unpackWordRun_code] at run
  exact run

theorem an_incomplete_suffix_clears_arbitrary_old_tags
    (rev : Word) (bit : Bool) (regs : Registers) :
    next^[rev.length + 2] (some (cfg (some .scan) regs [bit] rev [])) =
      some (Turing.haltList machine []) := by
  simpa [unpackWordRun, resultCode] using scan_iterate [bit] rev regs

theorem emitting_preserves_an_arbitrary_output_suffix
    (out : List (Option Tag)) (regs : Registers) :
    next^[3] (some (cfg (some .emit) regs [] [8, 1] out)) =
      some (Turing.haltList machine (none :: some (1 : Tag) :: some 8 :: out)) :=
  emit_iterate [8, 1] out regs

theorem clearing_preserves_an_arbitrary_output_suffix
    (out : List (Option Tag)) (regs : Registers) :
    next^[3] (some (cfg (some .clear) regs [] [15, 1] out)) =
      some (Turing.haltList machine out) :=
  clear_iterate [15, 1] out regs

theorem every_machine_stack_has_a_finite_alphabet (stack : StackId) :
    Finite (machine.Γ stack) := by
  change Finite (Alphabet stack)
  infer_instance

theorem each_reachable_stack_has_a_linear_bound (raw : Bits) (reached : machine.Cfg)
    (run : Turing.TM2.Reaches program (Turing.initList machine raw) reached) :
    (reached.stk .input).length ≤ raw.length + 1 ∧
      (reached.stk .reverse).length ≤ raw.length + 1 ∧
      (reached.stk .output).length ≤ raw.length + 1 := by
  have bounded := reachable_stackCells_le raw reached run
  unfold stackCells at bounded
  exact ⟨by omega, by omega, by omega⟩

theorem empty_success_requires_the_extra_workspace_cell :
    Turing.TM2.Reaches program (Turing.initList machine [])
        (Turing.haltList machine [none]) ∧
      stackCells (Turing.haltList machine [none]) = 1 ∧
      stackCells (Turing.haltList machine [none]) ≤ ([] : Bits).length + 1 ∧
      ¬ stackCells (Turing.haltList machine [none]) ≤ ([] : Bits).length := by
  have first : machine.step (Turing.initList machine []) =
      some (cfg (some .emit) zeroRegisters [] [] []) := by
    rw [initList_eq]
    exact scan_step_nil [] [] zeroRegisters
  have last : machine.step (cfg (some .emit) zeroRegisters [] [] []) =
      some (Turing.haltList machine [none]) := by
    rw [haltList_eq]
    exact emit_step_nil [] [] zeroRegisters
  have reached : Turing.TM2.Reaches program (Turing.initList machine [])
      (Turing.haltList machine [none]) := by
    change Relation.ReflTransGen
      (fun before after : machine.Cfg => machine.step before = some after) _ _
    refine Relation.ReflTransGen.head
      (b := cfg (some .emit) zeroRegisters [] [] []) ?_ ?_
    · exact first
    · exact Relation.ReflTransGen.single last
  have cells : stackCells (Turing.haltList machine [none]) = 1 := by
    rw [haltList_eq]
    rfl
  refine ⟨reached, cells,
    reachable_stackCells_le [] (Turing.haltList machine [none]) reached, ?_⟩
  rw [cells]
  decide

/-! An outer absent configuration is a post-halt observation, not an output code. -/

theorem a_post_halt_step_discards_the_actual_result (raw : Bits) :
    next^[runSteps raw + 1] (some (Turing.initList machine raw)) = none := by
  rw [Function.iterate_succ_apply', machine_run]
  rfl

theorem empty_success_is_present_before_the_post_halt_step :
    next^[2] (some (Turing.initList machine [])) =
        some (Turing.haltList machine [none]) ∧
      next^[3] (some (Turing.initList machine [])) = none :=
  ⟨machine_run_code [], a_post_halt_step_discards_the_actual_result []⟩

/-- Even the identity machine satisfies the outer-none target on every input. -/
def identityMachineOuterNoneInTime (raw : Bits) :
    Turing.TM2OutputsInTime (Turing.idComputer Bool) raw none 2 where
  steps := 2
  evals_in_steps := rfl
  steps_le_m := by decide

theorem identity_outer_none_does_not_mean_empty_rejection :
    (Turing.idComputer Bool).step (Turing.initList (Turing.idComputer Bool) [true]) =
        some (Turing.haltList (Turing.idComputer Bool) [true]) ∧
      Turing.haltList (Turing.idComputer Bool) [true] ≠
        Turing.haltList (Turing.idComputer Bool) [] := by
  refine ⟨rfl, ?_⟩
  intro equal
  have impossible : ([true] : List Bool) = [] :=
    congrArg (fun cfg : (Turing.idComputer Bool).Cfg => cfg.stk ()) equal
  cases impossible

theorem source_work_and_machine_steps_are_distinct :
    unpackWordRun (wordBits [0]) = (some [0], 6) ∧
      next^[4] (some (Turing.initList machine (wordBits [0]))) =
        some (Turing.haltList machine [none, some (0 : Tag)]) ∧
      next^[5] (some (Turing.initList machine (wordBits [0]))) = none :=
  ⟨unpackWordRun_code [0], machine_run_code [0],
    a_post_halt_step_discards_the_actual_result (wordBits [0])⟩

/-! Uniform evidence retains arbitrary raw inputs and uses the constructed records. -/

theorem every_raw_input_has_an_actual_linear_run (raw : Bits) :
    ∃ steps, steps ≤ raw.length + 2 ∧
      next^[steps] (some (Turing.initList machine raw)) =
        some (Turing.haltList machine (resultCode (unpackWordRun raw).1)) := by
  let evidence := outputsInTime raw
  exact ⟨evidence.steps, evidence.steps_le_m, evidence.evals_in_steps⟩

theorem every_raw_input_has_the_declared_transition_count (raw : Bits) :
    next^[2 * (raw.length / 4) + 2] (some (Turing.initList machine raw)) =
      some (Turing.haltList machine (resultCode (unpackWordRun raw).1)) :=
  machine_run raw

theorem every_raw_input_uses_one_polynomial_machine (raw : Bits) :
    ∃ steps, steps ≤ computableInPolyTime.time.eval raw.length ∧
      (fun cfg : Option computableInPolyTime.tm.Cfg =>
        cfg.bind computableInPolyTime.tm.step)^[steps]
        (some (Turing.initList computableInPolyTime.tm
          (raw.map computableInPolyTime.inputAlphabet.invFun))) =
        some (Turing.haltList computableInPolyTime.tm
          ((resultCode (unpackWordRun raw).1).map
            computableInPolyTime.outputAlphabet.invFun)) := by
  let evidence := computableInPolyTime.outputsFun raw
  exact ⟨evidence.steps, evidence.steps_le_m, evidence.evals_in_steps⟩

/-- The polynomial record itself produces the intended encoded word output. -/
noncomputable def encodedWordOutputsInTime (word : Word) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((wordBits word).map computableInPolyTime.inputAlphabet.invFun)
      (some ((none :: word.map some).map computableInPolyTime.outputAlphabet.invFun))
      (computableInPolyTime.time.eval (4 * word.length)) := by
  have evidence := computableInPolyTime.outputsFun (wordBits word)
  simpa only [id_eq, unpackWordRun_code, wordBits_length, resultCode] using evidence

end Examples.RotationCertificateBitDecoderMachine
