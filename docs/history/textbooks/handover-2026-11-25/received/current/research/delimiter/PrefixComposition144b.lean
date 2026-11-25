import NativeLoops144b

/-!
All actual prelude prefixes, complete physical occupancy, and composition with
the existing genuine controller initialization. UNCOMPILED repair2 proof draft.
No desired run, time or space bound is an assumption of the final results.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.DelimiterPreludeDraft.GeneralProof1

open Resources.BinaryCounter (Bits)

variable {R : Type} [Fintype R]

def BoundaryWitness (initial : R) (raw : Raw) (n : Nat) : Prop :=
  ∃ reached, next^[n] (some (Turing.initList (machine initial) raw)) = some reached ∧
    PreludeInvariant initial raw n reached

theorem prefix_witness (initial : R) (input : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ input.length) :
    BoundaryWitness initial (input.map some ++ tail) n := by
  refine ⟨_, prefix_from_init initial input tail n within, ?_⟩
  simpa only [List.length_take, Nat.min_eq_left within] using
    (PreludeInvariant.prefix (initial := initial) (raw := input.map some ++ tail)
      (input.take n) ((input.drop n).map some ++ tail) (bits_split_append input tail n))

theorem certificate_witness (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ cert.length) :
    BoundaryWitness initial (literalPair input cert ++ tail) (input.length + 1 + n) := by
  refine ⟨_, certificate_prefix initial input cert tail n within, ?_⟩
  simpa only [List.length_take, Nat.min_eq_left within] using
    (PreludeInvariant.certificate (initial := initial) (raw := literalPair input cert ++ tail)
      input (cert.take n) ((cert.drop n).map some ++ tail) (pair_split_append input cert tail n))

theorem reverse_witness (initial : R) (input cert : Bits) (n : Nat)
    (within : n ≤ (BitPairFraming.frame input cert).length) :
    BoundaryWitness initial (literalPair input cert) ((literalPair input cert).length + 1 + n) := by
  exact ⟨_, valid_reverse_prefix initial input cert n within,
    PreludeInvariant.reverse input cert n rfl within⟩

theorem drain_input_witness (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ tail.length) :
    BoundaryWitness initial (literalPair input cert ++ none :: tail)
      (input.length + cert.length + 2 + n) := by
  exact ⟨_, repeated_input_prefix initial input cert tail n within,
    PreludeInvariant.drainInput input cert tail n rfl within⟩

theorem drain_missing_witness (initial : R) (input : Bits) (n : Nat)
    (within : n ≤ (BitPairFraming.escapeBits input).length) :
    BoundaryWitness initial (input.map some) (input.length + 1 + n) := by
  refine ⟨_, missing_drain_prefix initial input n within, ?_⟩
  simpa only [List.length_map] using
    (PreludeInvariant.drainMissing (initial := initial) (raw := input.map some) input n rfl within)

theorem drain_repeated_witness (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ (BitPairFraming.frame input cert).length) :
    BoundaryWitness initial (literalPair input cert ++ none :: tail)
      ((literalPair input cert ++ none :: tail).length + 1 + n) := by
  exact ⟨_, repeated_work_prefix initial input cert tail n within,
    PreludeInvariant.drainRepeated input cert tail n rfl within⟩

theorem handoff_invariant (initial : R) (raw : Raw) :
    PreludeInvariant initial raw (preludeSteps raw)
      (Turing.initList (oldMachine initial) (handoffWord raw)) := by
  rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
  · have count : (input.map some : Raw).length + 2 * input.length + 2 =
        preludeSteps (input.map some) := by
      rw [List.length_map, preludeSteps_missing]
      omega
    have timed : PreludeInvariant initial (input.map some) (preludeSteps (input.map some))
        (Turing.initList (oldMachine initial) [] : Cfg R) :=
      count ▸ (PreludeInvariant.handoffMissing (initial := initial)
        (raw := input.map some) input rfl)
    have transported := congrArg
      (fun word : Bits => PreludeInvariant initial (input.map some)
        (preludeSteps (input.map some)) (Turing.initList (oldMachine initial) word : Cfg R))
      (handoffWord_missing input)
    exact transported.mpr timed
  · have timed : PreludeInvariant initial (literalPair input cert)
        (preludeSteps (literalPair input cert))
        (Turing.initList (oldMachine initial) (BitPairFraming.frame input cert) : Cfg R) :=
      (preludeSteps_pair_frame input cert).symm ▸
        (PreludeInvariant.handoffValid (initial := initial) (raw := literalPair input cert)
          input cert rfl)
    have transported := congrArg
      (fun word : Bits => PreludeInvariant initial (literalPair input cert)
        (preludeSteps (literalPair input cert))
        (Turing.initList (oldMachine initial) word : Cfg R)) (handoffWord_pair input cert)
    exact transported.mpr timed
  · have timed : PreludeInvariant initial (literalPair input cert ++ none :: tail)
        (preludeSteps (literalPair input cert ++ none :: tail))
        (Turing.initList (oldMachine initial) [] : Cfg R) :=
      (preludeSteps_repeated_frame input cert tail).symm ▸
        (PreludeInvariant.handoffRepeated (initial := initial)
          (raw := literalPair input cert ++ none :: tail) input cert tail rfl)
    have transported := congrArg
      (fun word : Bits => PreludeInvariant initial (literalPair input cert ++ none :: tail)
        (preludeSteps (literalPair input cert ++ none :: tail))
        (Turing.initList (oldMachine initial) word : Cfg R))
      (handoffWord_repeated input cert tail)
    exact transported.mpr timed

theorem handoff_witness (initial : R) (raw : Raw) :
    BoundaryWitness initial raw (preludeSteps raw) :=
  ⟨_, prelude_handoff initial raw, handoff_invariant initial raw⟩

/-- Every inclusive native prefix is one of the exact complete-state rows.
The phase split uses the independently fixed clocks from the actual loops. -/
theorem prelude_boundary (initial : R) (raw : Raw) (n : Nat)
    (within : n ≤ preludeSteps raw) : BoundaryWitness initial raw n := by
  by_cases final : n = preludeSteps raw
  · subst n
    exact handoff_witness initial raw
  have strict : n < preludeSteps raw := by omega
  rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
  · by_cases prefixPart : n ≤ input.length
    · simpa only [List.append_nil] using prefix_witness initial input [] n prefixPart
    · have work : n - (input.length + 1) ≤ (BitPairFraming.escapeBits input).length := by
        rw [BitPairFraming.escapeBits_length]
        rw [preludeSteps_missing] at strict
        omega
      have count : input.length + 1 + (n - (input.length + 1)) = n := by omega
      simpa only [count] using
        drain_missing_witness initial input (n - (input.length + 1)) work
  · by_cases prefixPart : n ≤ input.length
    · simpa only [literalPair, List.append_assoc, List.singleton_append] using
        prefix_witness initial input (none :: cert.map some) n prefixPart
    · by_cases certPart : n ≤ input.length + 1 + cert.length
      · have suffix : n - (input.length + 1) ≤ cert.length := by omega
        have count : input.length + 1 + (n - (input.length + 1)) = n := by omega
        simpa only [List.append_nil, count] using
          certificate_witness initial input cert [] (n - (input.length + 1)) suffix
      · have lengthEq := literalPair_length input cert
        have start : (literalPair input cert).length + 1 ≤ n := by omega
        have work : n - ((literalPair input cert).length + 1) ≤
            (BitPairFraming.frame input cert).length := by
          rw [preludeSteps_pair_frame] at strict
          omega
        have count : (literalPair input cert).length + 1 +
            (n - ((literalPair input cert).length + 1)) = n := by omega
        simpa only [count] using reverse_witness initial input cert
          (n - ((literalPair input cert).length + 1)) work
  · by_cases prefixPart : n ≤ input.length
    · simpa only [literalPair, List.append_assoc, List.cons_append, List.nil_append] using
        prefix_witness initial input (none :: (cert.map some ++ none :: tail)) n prefixPart
    · by_cases certPart : n ≤ input.length + 1 + cert.length
      · have suffix : n - (input.length + 1) ≤ cert.length := by omega
        have count : input.length + 1 + (n - (input.length + 1)) = n := by omega
        simpa only [count] using certificate_witness initial input cert (none :: tail)
          (n - (input.length + 1)) suffix
      · by_cases inputPart : n ≤ input.length + cert.length + 2 + tail.length
        · have suffix : n - (input.length + cert.length + 2) ≤ tail.length := by omega
          have count : input.length + cert.length + 2 +
              (n - (input.length + cert.length + 2)) = n := by omega
          simpa only [count] using drain_input_witness initial input cert tail
            (n - (input.length + cert.length + 2)) suffix
        · have lengthEq := repeated_length input cert tail
          have start : (literalPair input cert ++ none :: tail).length + 1 ≤ n := by omega
          have work : n - ((literalPair input cert ++ none :: tail).length + 1) ≤
              (BitPairFraming.frame input cert).length := by
            rw [preludeSteps_repeated_frame] at strict
            omega
          have count : (literalPair input cert ++ none :: tail).length + 1 +
              (n - ((literalPair input cert ++ none :: tail).length + 1)) = n := by omega
          simpa only [count] using drain_repeated_witness initial input cert tail
            (n - ((literalPair input cert ++ none :: tail).length + 1)) work

theorem callerContext_cells (raw : Raw) (work : Bits) :
    FrontEndStreamMachine.contextCells (callerContext raw work) = raw.length + work.length := by
  change (∑ k ∈ ({.input, .work} : Finset CallerStore), (callerContext raw work k).length) = _
  simp [callerContext]

omit [Fintype R] in
theorem state_stackCells (q : CallerPhase) (initial : R) (seen : Scratch)
    (raw : Raw) (work framed : Bits) :
    FrontEndStreamMachine.stackCells (state q initial seen raw work framed) =
      raw.length + work.length + framed.length := by
  rw [state, FrontEndStreamMachine.stackCells_cfg, callerContext_cells]
  simp only [FrontEndStreamMachine.localCells, List.length_nil, Nat.add_zero]
  omega

theorem old_init_stackCells (initial : R) (framed : Bits) :
    FrontEndStreamMachine.stackCells (Turing.initList (oldMachine initial) framed) = framed.length := by
  have transported := congrArg (fun c : Cfg R => FrontEndStreamMachine.stackCells c)
    (oldMachine_initList_eq initial framed)
  calc
    FrontEndStreamMachine.stackCells (Turing.initList (oldMachine initial) framed) =
        FrontEndStreamMachine.stackCells
          (FrontEndStreamMachine.cfg (some oldMain)
            (FrontEndStreamMachine.initialRegisters (none, initial))
            { framedRaw := framed } (callerContext [] [])) := transported
    _ = framed.length := by
      rw [FrontEndStreamMachine.stackCells_cfg, callerContext_cells]
      simp only [FrontEndStreamMachine.localCells, List.length_nil, Nat.add_zero]

/-- Physical total occupancy follows from the complete invariant, including
the actual input/work stores and all sixteen original stores. -/
theorem invariant_stackCells (initial : R) (raw : Raw) (n : Nat) (reached : Cfg R)
    (shape : PreludeInvariant initial raw n reached) :
    FrontEndStreamMachine.stackCells reached ≤ 2 * raw.length := by
  cases shape with
  | «prefix» before rest whole =>
      have hlength := congrArg List.length whole
      simp only [List.length_map, List.length_append] at hlength
      simp only [state_stackCells, List.length_reverse, BitPairFraming.escapeBits_length,
        List.length_nil]
      omega
  | certificate input before rest whole =>
      have hlength := congrArg List.length whole
      simp only [List.length_append, literalPair_length] at hlength
      simp only [state_stackCells, List.length_reverse, BitPairFraming.frame_length,
        List.length_nil]
      omega
  | reverse input cert j whole within =>
      have hlength := congrArg List.length whole
      rw [literalPair_length] at hlength
      have frameLength := BitPairFraming.frame_length input cert
      simp only [state_stackCells, List.length_nil, List.length_reverse, List.length_drop,
        List.length_take, Nat.min_eq_left within]
      omega
  | drainInput input cert tail j whole within =>
      have hlength := congrArg List.length whole
      simp only [List.length_append, literalPair_length, List.length_cons] at hlength
      simp only [state_stackCells, List.length_drop, List.length_reverse,
        BitPairFraming.frame_length, List.length_nil]
      omega
  | drainMissing input j whole within =>
      have hlength := congrArg List.length whole
      rw [List.length_map] at hlength
      simp only [state_stackCells, List.length_nil, List.length_drop, List.length_reverse,
        BitPairFraming.escapeBits_length]
      omega
  | drainRepeated input cert tail j whole within =>
      have hlength := congrArg List.length whole
      simp only [List.length_append, literalPair_length, List.length_cons] at hlength
      simp only [state_stackCells, List.length_nil, List.length_drop, List.length_reverse,
        BitPairFraming.frame_length]
      omega
  | handoffValid input cert whole =>
      have hlength := congrArg List.length whole
      rw [literalPair_length] at hlength
      rw [old_init_stackCells, BitPairFraming.frame_length]
      omega
  | handoffMissing input whole =>
      have emptyCells : FrontEndStreamMachine.stackCells
          (Turing.initList (oldMachine initial) ([] : Bits) : Cfg R) = 0 :=
        old_init_stackCells initial []
      exact emptyCells.le.trans (Nat.zero_le _)
  | handoffRepeated input cert tail whole =>
      have emptyCells : FrontEndStreamMachine.stackCells
          (Turing.initList (oldMachine initial) ([] : Bits) : Cfg R) = 0 :=
        old_init_stackCells initial []
      exact emptyCells.le.trans (Nat.zero_le _)

/-- The original proposed prefix proposition is supplied by actual loop runs
and the complete invariant, not by the independent reference model. -/
theorem prefix_obligation : PrefixObligation (R := R) := by
  intro initial raw n within
  obtain ⟨reached, executed, shape⟩ := prelude_boundary initial raw n within
  exact ⟨reached, executed, shape, invariant_stackCells initial raw n reached shape⟩

theorem prelude_prefix_cells (initial : R) (raw : Raw) (n : Nat)
    (within : n ≤ preludeSteps raw) (reached : Cfg R)
    (executed : next^[n] (some (Turing.initList (machine initial) raw)) = some reached) :
    FrontEndStreamMachine.stackCells reached ≤ 2 * raw.length := by
  obtain ⟨actual, actualRun, _, cells⟩ := prefix_obligation initial raw n within
  have same : actual = reached := Option.some.inj (actualRun.symm.trans executed)
  simpa only [same] using cells

/-- Literal complete native run: paid preprocessing followed by the old
genuine initializer theorem on the exact word produced by preprocessing. -/
theorem total_iterate (initial : R) (raw : Raw) :
    next^[totalSourceSteps raw] (some (Turing.initList (machine initial) raw)) =
      some (Turing.haltList (machine initial) [verifyDelimited raw]) := by
  have suffix : next^[FrontEndStreamMachine.runSteps (handoffWord raw)]
      (some (Turing.initList (oldMachine initial) (handoffWord raw))) =
      some (Turing.haltList (oldMachine initial)
        [BitPairFraming.verifyFramed (handoffWord raw)]) :=
    FrontEndStreamMachine.init_iterate caller (none, initial) (handoffWord raw)
  have answerEq := congrArg (fun b : Bool => [b]) (verifyFramed_handoffWord raw)
  have oldAnswer := congrArg
    (fun word : Bits => (Turing.haltList (oldMachine initial) word : Cfg R)) answerEq
  have endpoint := congrArg (fun c : Cfg R => some c)
    (oldAnswer.trans (haltList_eq_old initial [verifyDelimited raw]).symm)
  exact (run_trans (prelude_handoff initial raw) suffix).trans endpoint

/-- The source time polynomial follows from the real prelude clock and the
existing universal controller bound. No input-validity premise is needed. -/
theorem totalSourceSteps_le (raw : Raw) : totalSourceSteps raw ≤ sourceTimeBound raw.length := by
  have prelude := preludeSteps_le raw
  have controller := FrontEndStreamMachine.runSteps_le (handoffWord raw)
  have lengthBound := handoffWord_length_le raw
  have squareBound := Nat.mul_le_mul lengthBound lengthBound
  unfold totalSourceSteps sourceTimeBound
  nlinarith

/-- Compose the actual old peak theorem after the proved complete handoff.
Every reached configuration, including live halt, has bounded total occupancy. -/
theorem total_prefix_cells (initial : R) (raw : Raw) :
    FrontEndStreamMachine.PrefixProperty caller
      (fun c => FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1)
      (Turing.initList (machine initial) raw) (totalSourceSteps raw) := by
  have before : FrontEndStreamMachine.PrefixProperty caller
      (fun c => FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1)
      (Turing.initList (machine initial) raw) (preludeSteps raw) := by
    intro n within reached executed
    exact (prelude_prefix_cells initial raw n within reached executed).trans (Nat.le_max_left _ _)
  have after : FrontEndStreamMachine.PrefixProperty caller
      (fun c => FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1)
      (Turing.initList (oldMachine initial) (handoffWord raw))
      (FrontEndStreamMachine.runSteps (handoffWord raw)) := by
    intro n within reached executed
    have bound : FrontEndStreamMachine.stackCells reached ≤ max (handoffWord raw).length 1 :=
      (FrontEndStreamMachine.init_peak caller (none, initial) (handoffWord raw)).1
        n within reached executed
    exact bound.trans (max_le_max (handoffWord_length_le raw) (Nat.le_refl 1))
  exact FrontEndStreamMachine.PrefixProperty.trans caller (prelude_handoff initial raw) before after

def outputsInTime (initial : R) (raw : Raw) :
    Turing.TM2OutputsInTime (machine initial) raw (some [verifyDelimited raw])
      (sourceTimeBound raw.length) where
  steps := totalSourceSteps raw
  evals_in_steps := total_iterate initial raw
  steps_le_m := totalSourceSteps_le raw

theorem outputsInTime_steps (initial : R) (raw : Raw) :
    (outputsInTime initial raw).steps = totalSourceSteps raw := rfl

theorem total_outer_none (initial : R) (raw : Raw) :
    next^[totalSourceSteps raw + 1] (some (Turing.initList (machine initial) raw)) = none := by
  rw [Function.iterate_succ_apply', total_iterate]
  rfl

theorem literal_pair_output (initial : R) (input cert : Bits) :
    next^[totalSourceSteps (literalPair input cert)]
        (some (Turing.initList (machine initial) (literalPair input cert))) =
      some (Turing.haltList (machine initial) [(verifyBitsRun input cert).1]) := by
  have endpoint := congrArg
    (fun b : Bool => (some (Turing.haltList (machine initial) [b]) : Option (Cfg R)))
    (verifyDelimited_pair input cert)
  exact (total_iterate initial (literalPair input cert)).trans endpoint

theorem malformed_output (initial : R) (raw : Raw) (malformed : splitLiteral raw = none) :
    next^[totalSourceSteps raw] (some (Turing.initList (machine initial) raw)) =
      some (Turing.haltList (machine initial) [false]) := by
  have answerEq : verifyDelimited raw = false := by rw [verifyDelimited, malformed]
  have endpoint := congrArg
    (fun b : Bool => (some (Turing.haltList (machine initial) [b]) : Option (Cfg R))) answerEq
  exact (total_iterate initial raw).trans endpoint

end Resources.RotationCertificate.DelimiterPreludeDraft.GeneralProof1
