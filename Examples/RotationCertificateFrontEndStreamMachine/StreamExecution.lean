import Examples.RotationCertificateFrontEndStreamMachine.StreamCertificates

/-!
# RotationCertificateFrontEndStreamMachine: StreamExecution
-/


namespace Examples.RotationCertificateFrontEndStreamMachine

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Exact actual Stream segments inside the common physical carrier -/

def StreamFixture.LocalRunExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (fixture : StreamFixture) (caller : Λ → Statement Γ Λ R)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  LocalRun caller fixture.ticks
    (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
      (fullReset regs) fixture.before ctx)
    (cfg (some (phaseLabel (resultPhase fixture.result))) (fullReset regs) fixture.after ctx)

def StreamFixture.RunExpected {K Λ R : Type} {Γ : K → Type}
    (fixture : StreamFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  Runs transition
    (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
      (fullReset regs) fixture.before ctx) fixture.ticks
    (cfg (some (phaseLabel (resultPhase fixture.result))) (fullReset regs) fixture.after ctx)

def StreamFixture.PeakExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (fixture : StreamFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  ExactPeak transition
    (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
      (fullReset regs) fixture.before ctx) fixture.ticks (fixture.peak + externalCells ctx)

def streamProtectedCells (D : LocalData) : Nat :=
  D.framedRaw.length + D.frameFirstReverse.length + D.frameCertReverse.length +
    D.inputBits.length + D.certificateBits.length + D.inputRaw.length + D.bitsReverse.length

section ActualStreamTransport

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem common_stream_start_is_the_complete_view
    (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    streamCfg (Λ := Λ) (StreamMachine.cfg (some (StreamMachine.phaseLabel q))
      (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx)) =
      cfg (some (phaseLabel (streamPhase q))) regs D ctx := by
  simpa only [streamView, Option.map_some, streamLabelEquiv_phase] using
    streamCfg_view (Λ := Λ) (some (StreamMachine.phaseLabel q)) regs D ctx

omit caller [DecidableEq K] in
theorem common_stream_end_keeps_every_complement_word
    (bit : Bool) (D : LocalData) (E : StreamMachine.LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    streamCfg (Λ := Λ) (StreamMachine.cfg (some (StreamMachine.resultLabel bit))
      (StreamMachine.resetAll (StreamMachine.frontEndRegisterEquiv regs)) E (streamContext D ctx)) =
      cfg (some (phaseLabel (resultPhase bit))) (streamReset regs) (withStream D E) ctx := by
  simpa only [streamView, streamData_withStream, streamContext_withStream,
    frontEndRegisterEquiv_streamReset, Option.map_some, streamLabelEquiv_result] using
      streamCfg_view (Λ := Λ) (some (StreamMachine.resultLabel bit))
        (streamReset regs) (withStream D E) ctx

theorem an_existing_actual_stream_run_is_an_actual_common_carrier_run
    (fixture : Examples.RotationCertificateStreamMachine.RunFixture)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (sameInput : streamData D = fixture.before)
    (checked : fixture.RunExpected (StreamMachine.step localCaller)
      (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)) :
    LocalRun caller fixture.ticks
      (cfg (some (phaseLabel (streamPhase fixture.phase))) regs D ctx)
      (cfg (some (phaseLabel (resultPhase fixture.result)))
        (streamReset regs) (withStream D fixture.after) ctx) := by
  have original := StreamMachine.LocalRun.of_iterate localCaller checked.1 checked.2.2
  have transported := stream_localRun caller localCaller original
  change LocalRun caller fixture.ticks
    (streamCfg (StreamMachine.cfg (some (StreamMachine.phaseLabel fixture.phase))
      (StreamMachine.frontEndRegisterEquiv regs) fixture.before (streamContext D ctx)))
    (streamCfg (StreamMachine.cfg (some (StreamMachine.resultLabel fixture.result))
      (StreamMachine.resetAll (StreamMachine.frontEndRegisterEquiv regs)) fixture.after
      (streamContext D ctx))) at transported
  rw [← sameInput, common_stream_start_is_the_complete_view,
    common_stream_end_keeps_every_complement_word] at transported
  exact transported

variable [Fintype K]

/-- Transport all actual inclusive prefixes and the same attained peak witness. -/
theorem an_actual_stream_peak_is_preserved_by_the_full_stack_equivalence
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    {start finish : StreamCfg Γ Λ R} {ticks peak : Nat}
    (run : StreamMachine.LocalRun localCaller ticks start finish)
    (checked : Examples.RotationCertificateStreamMachine.ExactPeak
      (StreamMachine.step localCaller) start ticks peak) :
    ExactPeak (step caller) (streamCfg start) ticks peak := by
  have transport (n : Nat) (bound : n ≤ ticks) (reached : StreamCfg Γ Λ R)
      (executed : (StreamMachine.next localCaller)^[n] (some start) = some reached) :
      Runs (step caller) (streamCfg start) n (streamCfg reached) := by
    have equality := stream_prefix_transport caller localCaller n start
      (fun j strict => run.owned_prefix localCaller j (by omega))
    change (next caller)^[n] (some (streamCfg start)) = some (streamCfg reached)
    simpa only [executed, Option.map_some] using equality
  constructor
  · intro n bound reached executed
    obtain ⟨original, arrived⟩ : ∃ original,
        (StreamMachine.next localCaller)^[n] (some start) = some original := by
      by_cases last : n = ticks
      · subst n
        exact ⟨finish, run.iterate localCaller⟩
      · obtain ⟨original, arrived, _⟩ := run.owned_prefix localCaller n (by omega)
        exact ⟨original, arrived⟩
    have actual := transport n bound original arrived
    have same := Option.some.inj (executed.symm.trans actual)
    subst reached
    change Resources.RotationCertificate.FrontEndStreamMachine.stackCells (streamCfg original) ≤ peak
    rw [stackCells_streamCfg]
    exact checked.1 n bound original arrived
  · obtain ⟨n, original, bound, arrived, cells⟩ := checked.2
    refine ⟨n, streamCfg original, bound, transport n bound original arrived, ?_⟩
    change Resources.RotationCertificate.FrontEndStreamMachine.stackCells (streamCfg original) = peak
    rw [stackCells_streamCfg]
    exact cells

theorem a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells
    (fixture : Examples.RotationCertificateStreamMachine.RunFixture)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (sameInput : streamData D = fixture.before)
    (checkedRun : fixture.RunExpected (StreamMachine.step localCaller)
      (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))
    (checkedPeak : Examples.RotationCertificateStreamMachine.ExactPeak
      (StreamMachine.step localCaller)
      (fixture.start (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))
      fixture.ticks (fixture.peak + Examples.RotationCertificateStreamMachine.externalCells (streamContext D ctx))) :
    ExactPeak (step caller) (cfg (some (phaseLabel (streamPhase fixture.phase))) regs D ctx)
      fixture.ticks (fixture.peak + streamProtectedCells D + externalCells ctx) := by
  have run := StreamMachine.LocalRun.of_iterate localCaller checkedRun.1 checkedRun.2.2
  have peak := an_actual_stream_peak_is_preserved_by_the_full_stack_equivalence caller localCaller run checkedPeak
  change ExactPeak (step caller)
    (streamCfg (StreamMachine.cfg (some (StreamMachine.phaseLabel fixture.phase))
      (StreamMachine.frontEndRegisterEquiv regs) fixture.before (streamContext D ctx)))
    fixture.ticks (fixture.peak + Examples.RotationCertificateStreamMachine.externalCells (streamContext D ctx)) at peak
  rw [← sameInput, common_stream_start_is_the_complete_view] at peak
  have mass : Examples.RotationCertificateStreamMachine.externalCells (streamContext D ctx) =
      streamProtectedCells D + externalCells ctx := streamContext_cells D ctx
  simpa only [mass, Nat.add_assoc] using peak

end ActualStreamTransport

section LiteralStreamConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem rawV01_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV01.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a03
    rawV01.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a03_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV01.frontEndAfter ctx))

theorem rawV01_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV01.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV01_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV02_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV02.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV02
    rawV02.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV02.frontEndAfter ctx))

theorem rawV02_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV02.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV02_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV03.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a12
    rawV03.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV03.frontEndAfter ctx))

theorem rawV03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV03.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV03_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV04_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV04.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a13
    rawV04.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a13_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV04.frontEndAfter ctx))

theorem rawV04_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV04.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV04_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV05_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV05.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a18
    rawV05.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV05.frontEndAfter ctx))

theorem rawV05_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV05.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV05_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV06_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV06.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a19
    rawV06.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a19_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV06.frontEndAfter ctx))

theorem rawV06_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV06.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV06_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV07_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV07.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV07
    rawV07.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV07_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV07.frontEndAfter ctx))

theorem rawV07_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV07.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV07_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV08_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV08.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV08
    rawV08.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV08_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV08.frontEndAfter ctx))

theorem rawV08_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV08.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV08_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV09_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV09.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV09
    rawV09.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV09_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV09.frontEndAfter ctx))

theorem rawV09_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV09.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV09_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV10_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV10.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV10
    rawV10.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV10_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV10.frontEndAfter ctx))

theorem rawV10_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV10.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV10_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV11_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV11.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV11
    rawV11.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV11_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV11.frontEndAfter ctx))

theorem rawV11_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV11.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV11_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV12_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV12.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV12
    rawV12.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV12_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV12.frontEndAfter ctx))

theorem rawV12_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV12.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV12_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV13_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV13.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a17
    rawV13.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a17_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV13.frontEndAfter ctx))

theorem rawV13_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV13.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV13_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV14_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV14.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.r07
    rawV14.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r07_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV14.frontEndAfter ctx))

theorem rawV14_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV14.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV14_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV15_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV15.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV15
    rawV15.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV15_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV15.frontEndAfter ctx))

theorem rawV15_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV15.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV15_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV16_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV16.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV16
    rawV16.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV16_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV16.frontEndAfter ctx))

theorem rawV16_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV16.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV16_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV17_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV17.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a14
    rawV17.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a14_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV17.frontEndAfter ctx))

theorem rawV17_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV17.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV17_stream_actual_local_run caller regs ctx).iterate caller

theorem rawV18_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV18.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentV18
    rawV18.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV18_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV18.frontEndAfter ctx))

theorem rawV18_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match rawV18.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (rawV18_stream_actual_local_run caller regs ctx).iterate caller

theorem dirtyD00_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD00.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a18
    dirtyD00.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD00.stream.before ctx))

theorem dirtyD00_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD00.stream.RunExpected (step caller) regs ctx :=
  (dirtyD00_stream_actual_local_run caller regs ctx).iterate caller

theorem dirtyD01_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD01.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.r10
    dirtyD01.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r10_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD01.stream.before ctx))

theorem dirtyD01_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD01.stream.RunExpected (step caller) regs ctx :=
  (dirtyD01_stream_actual_local_run caller regs ctx).iterate caller

theorem dirtyD02_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD02.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentD02
    dirtyD02.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentD02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD02.stream.before ctx))

theorem dirtyD02_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD02.stream.RunExpected (step caller) regs ctx :=
  (dirtyD02_stream_actual_local_run caller regs ctx).iterate caller

theorem dirtyD03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD03.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a12
    dirtyD03.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD03.stream.before ctx))

theorem dirtyD03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD03.stream.RunExpected (step caller) regs ctx :=
  (dirtyD03_stream_actual_local_run caller regs ctx).iterate caller

theorem joinJ03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match joinJ03.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segmentJ03
    joinJ03.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentJ03_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext joinJ03.before ctx))

theorem joinJ03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match joinJ03.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (joinJ03_stream_actual_local_run caller regs ctx).iterate caller

variable [Fintype K]

theorem rawV01_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV01.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a03
    rawV01.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a03_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV01.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a03_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV01.frontEndAfter ctx))

theorem rawV02_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV02.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV02
    rawV02.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV02.frontEndAfter ctx))
    (StreamCertificates.segmentV02_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV02.frontEndAfter ctx))

theorem rawV03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV03.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a12
    rawV03.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV03.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a12_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV03.frontEndAfter ctx))

theorem rawV04_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV04.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a13
    rawV04.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a13_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV04.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a13_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV04.frontEndAfter ctx))

theorem rawV05_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV05.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a18
    rawV05.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV05.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a18_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV05.frontEndAfter ctx))

theorem rawV06_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV06.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a19
    rawV06.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a19_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV06.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a19_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV06.frontEndAfter ctx))

theorem rawV07_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV07.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV07
    rawV07.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV07_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV07.frontEndAfter ctx))
    (StreamCertificates.segmentV07_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV07.frontEndAfter ctx))

theorem rawV08_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV08.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV08
    rawV08.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV08_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV08.frontEndAfter ctx))
    (StreamCertificates.segmentV08_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV08.frontEndAfter ctx))

theorem rawV09_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV09.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV09
    rawV09.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV09_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV09.frontEndAfter ctx))
    (StreamCertificates.segmentV09_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV09.frontEndAfter ctx))

theorem rawV10_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV10.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV10
    rawV10.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV10_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV10.frontEndAfter ctx))
    (StreamCertificates.segmentV10_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV10.frontEndAfter ctx))

theorem rawV11_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV11.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV11
    rawV11.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV11_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV11.frontEndAfter ctx))
    (StreamCertificates.segmentV11_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV11.frontEndAfter ctx))

theorem rawV12_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV12.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV12
    rawV12.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV12_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV12.frontEndAfter ctx))
    (StreamCertificates.segmentV12_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV12.frontEndAfter ctx))

theorem rawV13_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV13.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a17
    rawV13.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a17_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV13.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a17_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV13.frontEndAfter ctx))

theorem rawV14_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV14.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.r07
    rawV14.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r07_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV14.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.r07_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV14.frontEndAfter ctx))

theorem rawV15_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV15.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV15
    rawV15.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV15_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV15.frontEndAfter ctx))
    (StreamCertificates.segmentV15_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV15.frontEndAfter ctx))

theorem rawV16_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV16.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV16
    rawV16.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV16_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV16.frontEndAfter ctx))
    (StreamCertificates.segmentV16_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV16.frontEndAfter ctx))

theorem rawV17_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV17.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a14
    rawV17.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a14_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV17.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a14_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV17.frontEndAfter ctx))

theorem rawV18_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV18.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentV18
    rawV18.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentV18_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV18.frontEndAfter ctx))
    (StreamCertificates.segmentV18_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext rawV18.frontEndAfter ctx))

theorem dirtyD00_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD00.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a18
    dirtyD00.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD00.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.a18_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD00.stream.before ctx))

theorem dirtyD01_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD01.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.r10
    dirtyD01.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r10_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD01.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.r10_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD01.stream.before ctx))

theorem dirtyD02_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD02.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentD02
    dirtyD02.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentD02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD02.stream.before ctx))
    (StreamCertificates.segmentD02_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD02.stream.before ctx))

theorem dirtyD03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirtyD03.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a12
    dirtyD03.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD03.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.a12_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirtyD03.stream.before ctx))

theorem joinJ03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match joinJ03.stream with | none => True | some segment => segment.PeakExpected (step caller) regs ctx) :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segmentJ03
    joinJ03.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segmentJ03_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext joinJ03.before ctx))
    (StreamCertificates.segmentJ03_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext joinJ03.before ctx))

end LiteralStreamConnections


end Examples.RotationCertificateFrontEndStreamMachine
