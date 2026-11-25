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

theorem raw_V01_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V01.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a03
    raw_V01.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a03_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V01.frontEndAfter ctx))

theorem raw_V01_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V01.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V01_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V02_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V02.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v02
    raw_V02.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V02.frontEndAfter ctx))

theorem raw_V02_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V02.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V02_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V03.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a12
    raw_V03.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V03.frontEndAfter ctx))

theorem raw_V03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V03.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V03_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V04_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V04.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a13
    raw_V04.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a13_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V04.frontEndAfter ctx))

theorem raw_V04_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V04.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V04_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V05_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V05.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a18
    raw_V05.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V05.frontEndAfter ctx))

theorem raw_V05_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V05.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V05_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V06_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V06.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a19
    raw_V06.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a19_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V06.frontEndAfter ctx))

theorem raw_V06_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V06.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V06_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V07_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V07.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v07
    raw_V07.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v07_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V07.frontEndAfter ctx))

theorem raw_V07_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V07.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V07_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V08_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V08.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v08
    raw_V08.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v08_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V08.frontEndAfter ctx))

theorem raw_V08_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V08.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V08_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V09_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V09.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v09
    raw_V09.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v09_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V09.frontEndAfter ctx))

theorem raw_V09_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V09.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V09_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V10_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V10.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v10
    raw_V10.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v10_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V10.frontEndAfter ctx))

theorem raw_V10_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V10.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V10_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V11_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V11.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v11
    raw_V11.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v11_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V11.frontEndAfter ctx))

theorem raw_V11_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V11.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V11_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V12_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V12.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v12
    raw_V12.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v12_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V12.frontEndAfter ctx))

theorem raw_V12_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V12.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V12_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V13_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V13.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a17
    raw_V13.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a17_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V13.frontEndAfter ctx))

theorem raw_V13_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V13.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V13_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V14_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V14.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.r07
    raw_V14.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r07_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V14.frontEndAfter ctx))

theorem raw_V14_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V14.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V14_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V15_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V15.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v15
    raw_V15.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v15_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V15.frontEndAfter ctx))

theorem raw_V15_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V15.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V15_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V16_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V16.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v16
    raw_V16.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v16_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V16.frontEndAfter ctx))

theorem raw_V16_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V16.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V16_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V17_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V17.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a14
    raw_V17.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a14_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V17.frontEndAfter ctx))

theorem raw_V17_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V17.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V17_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V18_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V18.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v18
    raw_V18.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v18_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V18.frontEndAfter ctx))

theorem raw_V18_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V18.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V18_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D00_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a18
    dirty_D00.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D00.stream.before ctx))

theorem dirty_D00_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.stream.RunExpected (step caller) regs ctx :=
  (dirty_D00_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D01_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.r10
    dirty_D01.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r10_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D01.stream.before ctx))

theorem dirty_D01_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.stream.RunExpected (step caller) regs ctx :=
  (dirty_D01_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D02_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_d02
    dirty_D02.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_d02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D02.stream.before ctx))

theorem dirty_D02_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.stream.RunExpected (step caller) regs ctx :=
  (dirty_D02_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a12
    dirty_D03.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D03.stream.before ctx))

theorem dirty_D03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.stream.RunExpected (step caller) regs ctx :=
  (dirty_D03_stream_actual_local_run caller regs ctx).iterate caller

theorem join_J03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match join_J03.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_j03
    join_J03.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_j03_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext join_J03.before ctx))

theorem join_J03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match join_J03.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (join_J03_stream_actual_local_run caller regs ctx).iterate caller

variable [Fintype K]

theorem raw_V01_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a03
    raw_V01.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a03_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V01.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a03_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V01.frontEndAfter ctx))

theorem raw_V02_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v02
    raw_V02.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V02.frontEndAfter ctx))
    (StreamCertificates.segment_v02_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V02.frontEndAfter ctx))

theorem raw_V03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a12
    raw_V03.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V03.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a12_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V03.frontEndAfter ctx))

theorem raw_V04_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a13
    raw_V04.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a13_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V04.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a13_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V04.frontEndAfter ctx))

theorem raw_V05_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a18
    raw_V05.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V05.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a18_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V05.frontEndAfter ctx))

theorem raw_V06_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a19
    raw_V06.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a19_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V06.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a19_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V06.frontEndAfter ctx))

theorem raw_V07_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v07
    raw_V07.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v07_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V07.frontEndAfter ctx))
    (StreamCertificates.segment_v07_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V07.frontEndAfter ctx))

theorem raw_V08_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v08
    raw_V08.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v08_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V08.frontEndAfter ctx))
    (StreamCertificates.segment_v08_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V08.frontEndAfter ctx))

theorem raw_V09_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v09
    raw_V09.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v09_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V09.frontEndAfter ctx))
    (StreamCertificates.segment_v09_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V09.frontEndAfter ctx))

theorem raw_V10_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v10
    raw_V10.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v10_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V10.frontEndAfter ctx))
    (StreamCertificates.segment_v10_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V10.frontEndAfter ctx))

theorem raw_V11_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v11
    raw_V11.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v11_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V11.frontEndAfter ctx))
    (StreamCertificates.segment_v11_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V11.frontEndAfter ctx))

theorem raw_V12_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v12
    raw_V12.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v12_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V12.frontEndAfter ctx))
    (StreamCertificates.segment_v12_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V12.frontEndAfter ctx))

theorem raw_V13_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a17
    raw_V13.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a17_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V13.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a17_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V13.frontEndAfter ctx))

theorem raw_V14_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.r07
    raw_V14.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r07_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V14.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.r07_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V14.frontEndAfter ctx))

theorem raw_V15_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v15
    raw_V15.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v15_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V15.frontEndAfter ctx))
    (StreamCertificates.segment_v15_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V15.frontEndAfter ctx))

theorem raw_V16_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v16
    raw_V16.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v16_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V16.frontEndAfter ctx))
    (StreamCertificates.segment_v16_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V16.frontEndAfter ctx))

theorem raw_V17_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a14
    raw_V17.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a14_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V17.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a14_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V17.frontEndAfter ctx))

theorem raw_V18_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v18
    raw_V18.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v18_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V18.frontEndAfter ctx))
    (StreamCertificates.segment_v18_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V18.frontEndAfter ctx))

theorem dirty_D00_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a18
    dirty_D00.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D00.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.a18_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D00.stream.before ctx))

theorem dirty_D01_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.r10
    dirty_D01.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r10_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D01.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.r10_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D01.stream.before ctx))

theorem dirty_D02_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_d02
    dirty_D02.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_d02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D02.stream.before ctx))
    (StreamCertificates.segment_d02_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D02.stream.before ctx))

theorem dirty_D03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a12
    dirty_D03.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D03.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.a12_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D03.stream.before ctx))

theorem join_J03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match join_J03.stream with | none => True | some segment => segment.PeakExpected (step caller) regs ctx) :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_j03
    join_J03.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_j03_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext join_J03.before ctx))
    (StreamCertificates.segment_j03_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext join_J03.before ctx))

end LiteralStreamConnections


end Examples.RotationCertificateFrontEndStreamMachine
