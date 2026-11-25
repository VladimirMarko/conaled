import Examples.RotationCertificateMoveApplyMachine.Fixtures

/-!
# RotationCertificateMoveApplyMachine: Boundaries
-/

namespace Examples.RotationCertificateMoveApplyMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.MoveApplyMachine

section PrincipalConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem independent_first_result_is_the_public_strict_first_result
    (start : Cfg Γ Λ R) (r : FinalResult) :
    FirstResult caller start r ↔ MoveApplyMachine.FirstResult caller start r := by
  constructor
  · rintro ⟨n, finish, first, label⟩
    exact ⟨n, finish, first.1, label, first.2.2⟩
  · rintro ⟨n, finish, run, label, earlier⟩
    refine ⟨n, finish, ⟨run, ?_, earlier⟩, label⟩
    rw [label]
    exact not_owned_result r

theorem principal_parser_failure_has_the_complete_dirty_endpoint_and_paid_clock
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    ParserFailureExpected caller regs ctx C O X F S Hd := by
  intro failed
  refine ⟨parse_failure_boundary caller C O X F S Hd regs ctx failed, ?_,
    parser_failure_source_cost C failed⟩
  exact local_run_gives_an_actual_first_return caller
    (run_of_none_localRun caller C O X F S Hd regs ctx failed) (not_owned_result parseFailure)

theorem principal_parser_success_pays_for_the_complete_dirty_position_entry
    (C rest : Word) (mv : RotationMove) (O : List Branch)
    (X F S : Word) (Hd : List Unit) :
    ParserSuccessExpected caller regs ctx C rest mv O X F S Hd := by
  intro parsed
  have count := MoveParserMachine.fullSteps_of_some C mv rest parsed
  have paidCount : MoveParserMachine.fullSteps C + 1 = 2 * mv.position.length + 4 := by omega
  refine ⟨count, parse_success_boundary caller C mv rest O X F S Hd regs ctx parsed, ?_, ?_⟩
  · simpa only [Runs, paidCount, entry, entryData, parsedData, data] using
      paid_position_entry caller C mv rest O X F S Hd regs ctx parsed
  · have actual := local_run_gives_an_actual_first_return caller
      (run_of_some_localRun caller C mv rest O X F S Hd regs ctx parsed)
      (phaseResult_not_owned (MoveApplyMachine.positionPhase (.seek mv.direction)) regs
        (parsedData mv rest (entryData C O X F S Hd)) ctx)
    simpa only [paidCount, entry, entryData, parsedData, positionData,
      data, phaseResult_reset, positionPhase, MoveApplyMachine.positionPhase] using actual

theorem first_parse_failure_iff_the_actual_source_parser_failed
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) parseFailure ↔
      (parseMoveRun C).1 = none := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact first_parseFailure_iff caller C O X F S Hd regs ctx

theorem first_rotation_failure_iff_the_actual_dirty_position_endpoint_failed
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) rotationFailure ↔
      ∃ mv rest, (parseMoveRun C).1 = some (mv, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek mv.direction)
          regs { source := X, saved := F, scratch := S, pending := Hd, path := mv.position ++ O }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .failure) := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact first_rotationFailure_iff caller C O X F S Hd regs ctx

theorem first_success_iff_the_actual_dirty_position_endpoint_succeeded
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) rotationSuccess ↔
      ∃ mv rest, (parseMoveRun C).1 = some (mv, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek mv.direction)
          regs { source := X, saved := F, scratch := S, pending := Hd, path := mv.position ++ O }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .success) := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact MoveApplyMachine.first_success_iff caller C O X F S Hd regs ctx

theorem each_of_the_three_first_results_fixes_the_same_complete_clock_and_configuration
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (r : FinalResult) (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n finish)
    (label : finish.l = some (resultLabel r)) :
    n = runSteps C O X F S Hd ∧ finish = runResult regs C O X F S Hd ctx :=
  first_result_complete caller (MoveApplyMachine.movePhase .start)
    (entryData C O X F S Hd) regs ctx r n finish first.1 label first.2.2

def principalInActualTime (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult regs C O X F S Hd ctx)) (runSteps C O X F S Hd) :=
  runInTimeExact caller C O X F S Hd regs ctx

theorem principal_typed_time_records_actual_composite_steps
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    (principalInActualTime caller regs ctx C O X F S Hd).steps = runSteps C O X F S Hd := rfl

end PrincipalConnections

section LiteralBoundarySteps
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

def parserObservationCaller : MoveParserMachine.External (MoveCallerLabel Λ) →
    MoveStatement Γ Λ R := fun _ => .halt
def positionObservationCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
    PositionStatement Γ Λ R := fun _ => .halt

theorem move_step_of_actual_component_observation
    (q : MoveParserMachine.Phase) (before after : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ)))
    (outRegs : MoveParserMachine.Registers (MoveCallerRegister R))
    (observed : MoveParserMachine.step parserObservationCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) before ctx) =
        some (moveView label outRegs after ctx)) :
    step caller (cfg (some (moveLabel q)) regs before ctx) =
      some (cfg (label.map moveLabelEquiv) (moveRegisterEquiv outRegs) after ctx) := by
  have actual := move_step_transport caller parserObservationCaller
    (moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) before ctx)
    (by trivial)
  rw [observed, Option.map_some, moveCfg_view, moveCfg_view] at actual
  simpa only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply] using actual

theorem move_start_direction_actual (d : RotationDirection) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel .start)) regs
      (data (directionTag d :: C) B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.scan d))) (resetMove regs) (data C B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller .start _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.scan d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.start_step_direction parserObservationCaller d C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_scan_branch_actual (d : RotationDirection) (b : Branch) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.scan d))) regs
      (data (branchTag b :: C) B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.scan d))) (resetMove regs) (data C (b :: B) O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.scan d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.scan d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.scan_step_branch parserObservationCaller d b C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_scan_end_actual (d : RotationDirection) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.scan d))) regs
      (data (endMoveTag :: C) B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.emit d))) (resetMove regs) (data C B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.scan d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.emit d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.scan_step_end parserObservationCaller d C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_scan_eof_actual (d : RotationDirection)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.scan d))) regs (data [] B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.undo d))) (resetMove regs) (data [] B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.scan d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.undo d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.scan_step_nil parserObservationCaller d B O
      (moveRegisterEquiv.symm regs) (moveContext (data [] B O X F S Hd) ctx))

theorem move_emit_empty_actual (d : RotationDirection) (C : Word)
    (O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.emit d))) regs (data C [] O X F S Hd) ctx) =
      some (cfg (some (dispatchLabel (.success d))) (resetMove regs) (data C [] O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.emit d) _ _ regs ctx
    (some (MoveParserMachine.resultLabel (.success d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.emit_step_nil parserObservationCaller d C O
      (moveRegisterEquiv.symm regs) (moveContext (data C [] O X F S Hd) ctx))

theorem move_undo_branch_actual (d : RotationDirection) (b : Branch) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.undo d))) regs (data C (b :: B) O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.undo d))) (resetMove regs)
        (data (branchTag b :: C) B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.undo d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.undo d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.undo_step_cons parserObservationCaller d b C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_undo_empty_actual (d : RotationDirection) (C : Word)
    (O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.undo d))) regs (data C [] O X F S Hd) ctx) =
      some (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (data (directionTag d :: C) [] O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.undo d) _ _ regs ctx
    (some (MoveParserMachine.resultLabel .failure))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.undo_step_nil parserObservationCaller d C O
      (moveRegisterEquiv.symm regs) (moveContext (data C [] O X F S Hd) ctx))

theorem every_position_observation_uses_the_actual_transported_primitive_step
    (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (positionLabel q)) regs D ctx) =
      some (cfg (some (positionLabelEquiv
        (PositionedRotationMachine.controlLabel (PositionedRotationMachine.advance q (positionData D)).1)))
        (reset regs) (setPositionData D (PositionedRotationMachine.advance q (positionData D)).2) ctx) := by
  have labels (control : PositionedRotationMachine.Control) :
      positionLabelEquiv (PositionedRotationMachine.controlLabel control) =
        positionControlLabel (Λ := Λ) control := by
    cases control <;> rfl
  rw [labels]
  exact position_advance_step caller q D regs ctx

end LiteralBoundarySteps

private theorem boundary_run_succ {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) {start before after : Cfg Γ Λ R}
    {n : Nat} (prior : Runs caller start n before)
    (one : step caller before = some after) : Runs caller start (n + 1) after := by
  change (next caller)^[n] (some start) = some before at prior
  change (next caller)^[n + 1] (some start) = some after
  rw [Function.iterate_succ_apply', prior, next_some, one]

section LiteralBoundaryRuns
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_left_literal_row_is_the_actual_reached_configuration
    (b : Boundary) (member : b ∈ leftBoundaries) :
    Runs caller
      (cfg (some (moveLabel .start)) regs (data [6,10,15] [] [] [1,0,1,15] [] [] []) ctx)
      b.tick (b.cfg regs ctx) := by
  let c0 : Cfg Γ Λ R := (⟨0, .inl (movePhase .start), data [6,10,15] [] [] [1,0,1,15] [] [] [], .original, 7, 11⟩ : Boundary).cfg regs ctx
  let c1 : Cfg Γ Λ R := (⟨1, .inl (movePhase (.scan .left)), data [10,15] [] [] [1,0,1,15] [] [] [], .parser, 6, 11⟩ : Boundary).cfg regs ctx
  let c2 : Cfg Γ Λ R := (⟨2, .inl (movePhase (.emit .left)), data [15] [] [] [1,0,1,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c3 : Cfg Γ Λ R := (⟨3, .inl (dispatchPhase (.success .left)), data [15] [] [] [1,0,1,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c4 : Cfg Γ Λ R := (⟨4, .inl (positionPhase (.seek .left)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c5 : Cfg Γ Λ R := (⟨5, .inl (positionPhase (.start .left)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c6 : Cfg Γ Λ R := (⟨6, .inl (positionPhase (.scanScratch .left)), data [15] [] [] [0,1,15] [] [] [()], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c7 : Cfg Γ Λ R := (⟨7, .inl (positionPhase .checkRight), data [15] [] [] [1,15] [] [0] [], .complete, 4, 7⟩ : Boundary).cfg regs ctx
  let c8 : Cfg Γ Λ R := (⟨8, .inl (positionPhase (.restoreScratch .successLeft)), data [15] [] [] [15] [] [0] [], .complete, 3, 5⟩ : Boundary).cfg regs ctx
  let c9 : Cfg Γ Λ R := (⟨9, .inl (positionPhase (.restoreScratch .successLeft)), data [15] [] [] [0,15] [] [] [], .complete, 3, 5⟩ : Boundary).cfg regs ctx
  let c10 : Cfg Γ Λ R := (⟨10, .inl (positionPhase (.restorePrefix .success)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  let c11 : Cfg Γ Λ R := (⟨11, .inr rotationSuccess, data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  have r0 : Runs caller c0 0 c0 := rfl
  have s1 : step caller c0 = some c1 := by
    dsimp only [c0, c1, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_start_direction_actual caller .left _ _ _ _ _ _ _ _ _
  have r1 := boundary_run_succ caller r0 s1
  have s2 : step caller c1 = some c2 := by
    dsimp only [c1, c2, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_end_actual caller .left _ _ _ _ _ _ _ _ _
  have r2 := boundary_run_succ caller r1 s2
  have s3 : step caller c2 = some c3 := by
    dsimp only [c2, c3, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_emit_empty_actual caller .left _ _ _ _ _ _ _ _
  have r3 := boundary_run_succ caller r2 s3
  have s4 : step caller c3 = some c4 := by
    dsimp only [c3, c4, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact dispatch_step caller _ _ _ _
  have r4 := boundary_run_succ caller r3 s4
  have s5 : step caller c4 = some c5 := by
    dsimp only [c4, c5, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r5 := boundary_run_succ caller r4 s5
  have s6 : step caller c5 = some c6 := by
    dsimp only [c5, c6, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r6 := boundary_run_succ caller r5 s6
  have s7 : step caller c6 = some c7 := by
    dsimp only [c6, c7, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r7 := boundary_run_succ caller r6 s7
  have s8 : step caller c7 = some c8 := by
    dsimp only [c7, c8, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r8 := boundary_run_succ caller r7 s8
  have s9 : step caller c8 = some c9 := by
    dsimp only [c8, c9, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r9 := boundary_run_succ caller r8 s9
  have s10 : step caller c9 = some c10 := by
    dsimp only [c9, c10, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r10 := boundary_run_succ caller r9 s10
  have s11 : step caller c10 = some c11 := by
    dsimp only [c10, c11, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r11 := boundary_run_succ caller r10 s11
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11

theorem every_right_literal_row_is_the_actual_reached_configuration
    (b : Boundary) (member : b ∈ rightBoundaries) :
    Runs caller
      (cfg (some (moveLabel .start)) regs (data [7,10,15] [] [] [1,1,0,15] [] [] []) ctx)
      b.tick (b.cfg regs ctx) := by
  let c0 : Cfg Γ Λ R := (⟨0, .inl (movePhase .start), data [7,10,15] [] [] [1,1,0,15] [] [] [], .original, 7, 11⟩ : Boundary).cfg regs ctx
  let c1 : Cfg Γ Λ R := (⟨1, .inl (movePhase (.scan .right)), data [10,15] [] [] [1,1,0,15] [] [] [], .parser, 6, 11⟩ : Boundary).cfg regs ctx
  let c2 : Cfg Γ Λ R := (⟨2, .inl (movePhase (.emit .right)), data [15] [] [] [1,1,0,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c3 : Cfg Γ Λ R := (⟨3, .inl (dispatchPhase (.success .right)), data [15] [] [] [1,1,0,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c4 : Cfg Γ Λ R := (⟨4, .inl (positionPhase (.seek .right)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c5 : Cfg Γ Λ R := (⟨5, .inl (positionPhase (.start .right)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c6 : Cfg Γ Λ R := (⟨6, .inl (positionPhase (.scanScratch .right)), data [15] [] [] [0,15] [] [] [()], .complete, 4, 8⟩ : Boundary).cfg regs ctx
  let c7 : Cfg Γ Λ R := (⟨7, .inl (positionPhase (.restoreScratch .successRight)), data [15] [] [] [1,15] [] [0] [], .complete, 4, 5⟩ : Boundary).cfg regs ctx
  let c8 : Cfg Γ Λ R := (⟨8, .inl (positionPhase (.restoreScratch .successRight)), data [15] [] [] [0,1,15] [] [] [], .complete, 4, 5⟩ : Boundary).cfg regs ctx
  let c9 : Cfg Γ Λ R := (⟨9, .inl (positionPhase (.restorePrefix .success)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  let c10 : Cfg Γ Λ R := (⟨10, .inr rotationSuccess, data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  have r0 : Runs caller c0 0 c0 := rfl
  have s1 : step caller c0 = some c1 := by
    dsimp only [c0, c1, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_start_direction_actual caller .right _ _ _ _ _ _ _ _ _
  have r1 := boundary_run_succ caller r0 s1
  have s2 : step caller c1 = some c2 := by
    dsimp only [c1, c2, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_end_actual caller .right _ _ _ _ _ _ _ _ _
  have r2 := boundary_run_succ caller r1 s2
  have s3 : step caller c2 = some c3 := by
    dsimp only [c2, c3, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_emit_empty_actual caller .right _ _ _ _ _ _ _ _
  have r3 := boundary_run_succ caller r2 s3
  have s4 : step caller c3 = some c4 := by
    dsimp only [c3, c4, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact dispatch_step caller _ _ _ _
  have r4 := boundary_run_succ caller r3 s4
  have s5 : step caller c4 = some c5 := by
    dsimp only [c4, c5, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r5 := boundary_run_succ caller r4 s5
  have s6 : step caller c5 = some c6 := by
    dsimp only [c5, c6, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r6 := boundary_run_succ caller r5 s6
  have s7 : step caller c6 = some c7 := by
    dsimp only [c6, c7, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r7 := boundary_run_succ caller r6 s7
  have s8 : step caller c7 = some c8 := by
    dsimp only [c7, c8, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r8 := boundary_run_succ caller r7 s8
  have s9 : step caller c8 = some c9 := by
    dsimp only [c8, c9, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r9 := boundary_run_succ caller r8 s9
  have s10 : step caller c9 = some c10 := by
    dsimp only [c9, c10, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r10 := boundary_run_succ caller r9 s10
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

theorem every_parser_failure_row_keeps_every_dirty_tree_store
    (b : Boundary) (member : b ∈ parseFailureBoundaries) :
    Runs caller (cfg (some (moveLabel .start)) regs (failureData [6,8,9] []) ctx)
      b.tick (b.cfg regs ctx) := by
  let c0 : Cfg Γ Λ R := (⟨0, .inl (movePhase .start), failureData [6,8,9] [], .original, 12, 14⟩ : Boundary).cfg regs ctx
  let c1 : Cfg Γ Λ R := (⟨1, .inl (movePhase (.scan .left)), failureData [8,9] [], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c2 : Cfg Γ Λ R := (⟨2, .inl (movePhase (.scan .left)), failureData [9] [.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c3 : Cfg Γ Λ R := (⟨3, .inl (movePhase (.scan .left)), failureData [] [.right,.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c4 : Cfg Γ Λ R := (⟨4, .inl (movePhase (.undo .left)), failureData [] [.right,.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c5 : Cfg Γ Λ R := (⟨5, .inl (movePhase (.undo .left)), failureData [9] [.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c6 : Cfg Γ Λ R := (⟨6, .inl (movePhase (.undo .left)), failureData [8,9] [], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c7 : Cfg Γ Λ R := (⟨7, .inl (dispatchPhase .failure), failureData [6,8,9] [], .parser, 12, 14⟩ : Boundary).cfg regs ctx
  let c8 : Cfg Γ Λ R := (⟨8, .inr parseFailure, failureData [6,8,9] [], .complete, 12, 12⟩ : Boundary).cfg regs ctx
  have r0 : Runs caller c0 0 c0 := rfl
  have s1 : step caller c0 = some c1 := by
    dsimp only [c0, c1, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_start_direction_actual caller .left _ _ _ _ _ _ _ _ _
  have r1 := boundary_run_succ caller r0 s1
  have s2 : step caller c1 = some c2 := by
    dsimp only [c1, c2, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_branch_actual caller .left .left _ _ _ _ _ _ _ _ _
  have r2 := boundary_run_succ caller r1 s2
  have s3 : step caller c2 = some c3 := by
    dsimp only [c2, c3, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_branch_actual caller .left .right _ _ _ _ _ _ _ _ _
  have r3 := boundary_run_succ caller r2 s3
  have s4 : step caller c3 = some c4 := by
    dsimp only [c3, c4, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_eof_actual caller .left _ _ _ _ _ _ _ _
  have r4 := boundary_run_succ caller r3 s4
  have s5 : step caller c4 = some c5 := by
    dsimp only [c4, c5, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_undo_branch_actual caller .left .right _ _ _ _ _ _ _ _ _
  have r5 := boundary_run_succ caller r4 s5
  have s6 : step caller c5 = some c6 := by
    dsimp only [c5, c6, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_undo_branch_actual caller .left .left _ _ _ _ _ _ _ _ _
  have r6 := boundary_run_succ caller r5 s6
  have s7 : step caller c6 = some c7 := by
    dsimp only [c6, c7, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_undo_empty_actual caller .left _ _ _ _ _ _ _ _
  have r7 := boundary_run_succ caller r6 s7
  have s8 : step caller c7 = some c8 := by
    dsimp only [c7, c8, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact dispatch_step caller _ _ _ _
  have r8 := boundary_run_succ caller r7 s8
  simp only [parseFailureBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8

theorem actual_prefix_has_the_exact_remaining_rank
    (start reached : Cfg Γ Λ R) (total n : Nat)
    (rank : remainingSteps start = total) (bound : n ≤ total)
    (executed : Runs caller start n reached) :
    remainingSteps reached = total - n ∧ (n < total ↔ Owned reached.l) := by
  have segment : LocalRun caller n start reached := LocalRun.of_iterate caller executed (by
    intro j strict
    exact LocalRun.owned_prefix caller (cfg_localRun caller start) j (by omega))
  have remaining := LocalRun.remaining caller segment
  have exactRank : remainingSteps reached = total - n := by omega
  refine ⟨exactRank, ?_⟩
  rw [← remainingSteps_pos_iff, exactRank]
  omega

omit [DecidableEq K] in
theorem literal_success_entry_ranks_are_eleven_and_ten :
    remainingSteps (cfg (Λ := Λ) (some (moveLabel .start)) regs
      (data [6,10,15] [] [] [1,0,1,15] [] [] []) ctx) = 11 ∧
    remainingSteps (cfg (Λ := Λ) (some (moveLabel .start)) regs
      (data [7,10,15] [] [] [1,1,0,15] [] [] []) ctx) = 10 := by
  constructor
  · change remainingSteps (cfg (Λ := Λ) (some (phaseLabel (movePhase .start))) regs _ ctx) = _
    rw [remainingSteps_phase_cfg]
    exact congrArg Evaluation.steps malformed_left_evaluation
  · change remainingSteps (cfg (Λ := Λ) (some (phaseLabel (movePhase .start))) regs _ ctx) = _
    rw [remainingSteps_phase_cfg]
    exact congrArg Evaluation.steps malformed_right_evaluation

omit [DecidableEq K] in
theorem literal_failure_entry_rank_is_eight :
    remainingSteps (cfg (Λ := Λ) (some (moveLabel .start)) regs (failureData [6,8,9] []) ctx) = 8 := by
  change remainingSteps (cfg (Λ := Λ) (some (phaseLabel (movePhase .start))) regs _ ctx) = _
  rw [remainingSteps_phase_cfg]
  simp [phaseSteps, evaluate, evaluateDispatch, moveFinish, moveScanFinish,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, MoveParserMachine.branchCount,
    parsePathRun, Resources.bind, pathTags, directionTag,
    rotateLeftTag, rotateRightTag, pathLeftTag, pathRightTag, endMoveTag,
    data, failureData, movePhase]

theorem all_literal_times_are_in_the_inclusive_first_prefix :
    (∀ b ∈ leftBoundaries, b.tick ≤ 11) ∧
      (∀ b ∈ rightBoundaries, b.tick ≤ 10) ∧
      (∀ b ∈ parseFailureBoundaries, b.tick ≤ 8) := by
  constructor
  · intro b member
    simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · constructor
    · intro b member
      simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro b member
      simp only [parseFailureBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end LiteralBoundaryRuns

/- One actual configuration carries every inclusive-prefix claim. -/
section PrefixConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem all_configuration_prefixes_have_one_shared_complete_witness
    (start : Cfg Γ Λ R) (n : Nat) : PrefixExpected caller start n :=
  fun bound => owned_prefix_frame caller start n bound

theorem every_dirty_prefix_is_independent_of_all_later_caller_bodies
    (other : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

theorem agreement_on_all_twenty_six_owned_bodies_transports_the_prefix
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (flip bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) :=
  ambient_prefix_eq caller ambient agrees start n bound

section Physical
variable [Fintype K]

theorem every_dirty_prefix_has_the_same_rank_frame_register_and_physical_witness
    (start : Cfg Γ Λ R) (n : Nat) : PrefixSpaceExpected caller start n :=
  fun bound => owned_prefix_space caller start n bound

omit [DecidableEq K] in
theorem every_local_store_and_every_protected_store_is_counted
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs D ctx) =
      D.certificate.length + D.moveReverse.length + D.path.length + D.source.length +
        D.saved.length + D.scratch.length + D.pending.length + contextCells ctx :=
  stackCells_cfg label regs D ctx

omit [DecidableEq K] in
theorem the_three_dispatch_potentials_have_the_exact_paid_drops
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (Λ := Λ) (some (dispatchLabel (.success d))) regs D ctx) =
        potential (cfg (Λ := Λ) (some (positionLabel (.seek d))) (reset regs) D ctx) + 2 ∧
      potential (cfg (Λ := Λ) (some (dispatchLabel .failure)) regs D ctx) =
        potential (cfg (Λ := Λ) (some (resultLabel parseFailure)) (reset regs) D ctx) + D.source.length :=
  ⟨dispatch_success_potential (Λ := Λ) d D regs ctx, dispatch_failure_potential (Λ := Λ) D regs ctx⟩

end Physical
end PrefixConnections

theorem the_two_actual_protected_contexts_have_seven_and_five_cells :
    contextCells authorContext = 7 ∧ contextCells independentContext = 5 := by
  constructor
  · simp only [contextCells, Fin.sum_univ_two]
    rfl
  · simp only [contextCells, Fin.sum_univ_two]
    rfl

private theorem boundary_physical_fields {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (b : Boundary)
    (cells : localCells b.stores = b.cells)
    (weight : (match b.control with
      | .inl q => localCells b.stores + phaseDebt q + phaseCredit q b.stores
      | .inr _ => localCells b.stores) = b.creditCells) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  rcases b with ⟨tick, control, D, stage, count, credit⟩
  change localCells D = count at cells
  rcases control with q | r
  · change localCells D + phaseDebt q + phaseCredit q D = credit at weight
    refine ⟨rfl, (fun _ => rfl), ?_, ?_⟩
    · change stackCells (cfg (Λ := Λ) _ _ D ctx) = count + contextCells ctx
      rw [stackCells_cfg, cells]
    · change potential (cfg (some (phaseLabel (Λ := Λ) q)) _ D ctx) = credit + contextCells ctx
      rw [potential_phase_cfg, weight]
  · change localCells D = credit at weight
    refine ⟨rfl, (fun _ => rfl), ?_, ?_⟩
    · change stackCells (cfg (Λ := Λ) _ _ D ctx) = count + contextCells ctx
      rw [stackCells_cfg, cells]
    · change potential (cfg (some (resultLabel (Λ := Λ) r)) _ D ctx) = credit + contextCells ctx
      rw [potential_result_cfg, weight]

section LiteralBoundaryPhysical
variable {K Λ R : Type} {Γ : K → Type} [Fintype K]
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_left_literal_row_has_its_fixed_physical_fields
    (b : Boundary) (member : b ∈ leftBoundaries) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boundary_physical_fields regs ctx _ rfl rfl

theorem every_right_literal_row_has_its_fixed_physical_fields
    (b : Boundary) (member : b ∈ rightBoundaries) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boundary_physical_fields regs ctx _ rfl rfl

theorem every_parser_failure_row_has_its_fixed_physical_fields
    (b : Boundary) (member : b ∈ parseFailureBoundaries) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  simp only [parseFailureBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boundary_physical_fields regs ctx _ rfl rfl

variable [DecidableEq K] (caller : External Λ → Statement Γ Λ R)

theorem every_left_literal_boundary_satisfies_the_complete_fixed_contract
    (b : Boundary) (member : b ∈ leftBoundaries) :
    b.Expected caller regs ctx (data [6,10,15] [] [] [1,0,1,15] [] [] []) 11 := by
  have executed := every_left_literal_row_is_the_actual_reached_configuration caller regs ctx b member
  have rank := actual_prefix_has_the_exact_remaining_rank caller _ _ 11 b.tick
    (literal_success_entry_ranks_are_eleven_and_ten (Λ := Λ) regs ctx).1
    (all_literal_times_are_in_the_inclusive_first_prefix.1 b member) executed
  have physical := every_left_literal_row_has_its_fixed_physical_fields (Λ := Λ) regs ctx b member
  exact ⟨executed, rank.1, rank.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

theorem every_right_literal_boundary_satisfies_the_complete_fixed_contract
    (b : Boundary) (member : b ∈ rightBoundaries) :
    b.Expected caller regs ctx (data [7,10,15] [] [] [1,1,0,15] [] [] []) 10 := by
  have executed := every_right_literal_row_is_the_actual_reached_configuration caller regs ctx b member
  have rank := actual_prefix_has_the_exact_remaining_rank caller _ _ 10 b.tick
    (literal_success_entry_ranks_are_eleven_and_ten (Λ := Λ) regs ctx).2
    (all_literal_times_are_in_the_inclusive_first_prefix.2.1 b member) executed
  have physical := every_right_literal_row_has_its_fixed_physical_fields (Λ := Λ) regs ctx b member
  exact ⟨executed, rank.1, rank.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

theorem every_parser_failure_boundary_satisfies_the_complete_fixed_contract
    (b : Boundary) (member : b ∈ parseFailureBoundaries) :
    b.Expected caller regs ctx (failureData [6,8,9] []) 8 := by
  have executed := every_parser_failure_row_keeps_every_dirty_tree_store caller regs ctx b member
  have rank := actual_prefix_has_the_exact_remaining_rank caller _ _ 8 b.tick
    (literal_failure_entry_rank_is_eight (Λ := Λ) regs ctx)
    (all_literal_times_are_in_the_inclusive_first_prefix.2.2 b member) executed
  have physical := every_parser_failure_row_has_its_fixed_physical_fields (Λ := Λ) regs ctx b member
  exact ⟨executed, rank.1, rank.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

end LiteralBoundaryPhysical

/- The same literal rows specialize to both independently fixed protected contexts. -/
theorem all_literal_boundaries_keep_both_distinct_contexts
    (author : AuthorCaller) (independent : ExampleCaller) (flag : Bool) :
    (∀ b ∈ leftBoundaries, b.Expected author (stale flag) authorContext
      (data [6,10,15] [] [] [1,0,1,15] [] [] []) 11) ∧
    (∀ b ∈ rightBoundaries, b.Expected author (stale flag) authorContext
      (data [7,10,15] [] [] [1,1,0,15] [] [] []) 10) ∧
    (∀ b ∈ parseFailureBoundaries, b.Expected author (stale flag) authorContext
      (failureData [6,8,9] []) 8) ∧
    (∀ b ∈ leftBoundaries, b.Expected independent (stale flag) independentContext
      (data [6,10,15] [] [] [1,0,1,15] [] [] []) 11) ∧
    (∀ b ∈ rightBoundaries, b.Expected independent (stale flag) independentContext
      (data [7,10,15] [] [] [1,1,0,15] [] [] []) 10) ∧
    (∀ b ∈ parseFailureBoundaries, b.Expected independent (stale flag) independentContext
      (failureData [6,8,9] []) 8) :=
  ⟨every_left_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) authorContext author,
    every_right_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) authorContext author,
    every_parser_failure_boundary_satisfies_the_complete_fixed_contract (stale flag) authorContext author,
    every_left_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) independentContext independent,
    every_right_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) independentContext independent,
    every_parser_failure_boundary_satisfies_the_complete_fixed_contract (stale flag) independentContext independent⟩


end Examples.RotationCertificateMoveApplyMachine
