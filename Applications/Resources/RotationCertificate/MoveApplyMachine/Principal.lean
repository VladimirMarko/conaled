import Applications.Resources.RotationCertificate.MoveApplyMachine.Represented

/-!
# MoveApplyMachine: Principal
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ### Complete principal data and represented endpoint views -/

/-- Principal entry has an empty parser reverse stack and arbitrary Position stores. -/
def entryData (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) : LocalData where
  certificate := raw
  path := path
  source := source
  saved := saved
  scratch := scratch
  pending := pending

def entry (regs : Registers R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (moveLabel .start)) regs (entryData raw path source saved scratch pending) ctx

/-- The parser's real success appends the old forward path; the other stores are retained. -/
def parsedData (move : RotationMove) (rest : Word) (D : LocalData) : LocalData :=
  { D with certificate := rest, moveReverse := [], path := move.position ++ D.path }

/-- A clean represented tree may still have arbitrary old path, saved word and two suffixes. -/
def representedEntryData (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word) : LocalData :=
  entryData (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] []

def representedFinalData (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word) : LocalData where
  certificate := certificateRest
  source := representedSource move oldPath s saved suffix
  path := PositionedRotationMachine.remainingPath (move.position ++ oldPath) s

def representedResult (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) : FinalResult :=
  if (representedValue move oldPath s).isSome then success else rotationFailure

@[simp] theorem parsedData_certificate (move : RotationMove) (rest : Word) (D : LocalData) :
    (parsedData move rest D).certificate = rest := rfl

@[simp] theorem parsedData_moveReverse (move : RotationMove) (rest : Word) (D : LocalData) :
    (parsedData move rest D).moveReverse = [] := rfl

@[simp] theorem parsedData_path (move : RotationMove) (rest : Word) (D : LocalData) :
    (parsedData move rest D).path = move.position ++ D.path := rfl

@[simp] theorem representedFinalData_source_length (move : RotationMove)
    (certificateRest : Word) (oldPath : List Branch) (s : BinaryTree Unit)
    (saved suffix : Word) :
    (representedFinalData move certificateRest oldPath s saved suffix).source.length =
      saved.length + 2 * s.numNodes + 1 + suffix.length :=
  representedSource_length move oldPath s saved suffix

theorem representedResult_of_none (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (failed : representedValue move oldPath s = none) :
    representedResult move oldPath s = rotationFailure := by
  simp only [representedResult, failed, Option.isSome_none, Bool.false_eq_true, ite_false]

theorem representedResult_of_some (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (returned : representedValue move oldPath s = some t) :
    representedResult move oldPath s = success := by
  simp only [representedResult, returned, Option.isSome_some, ite_true]

theorem representedResult_success_iff (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    representedResult move oldPath s = success ↔
      ∃ t, representedValue move oldPath s = some t := by
  cases actual : representedValue move oldPath s with
  | none => simp [representedResult, actual, success, rotationFailure]
  | some t => simp [representedResult, actual]

theorem representedResult_failure_iff (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    representedResult move oldPath s = rotationFailure ↔
      representedValue move oldPath s = none := by
  cases actual : representedValue move oldPath s with
  | none => simp [representedResult, actual]
  | some t => simp [representedResult, actual, success, rotationFailure]

theorem representedFinalData_of_some (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix : Word)
    (returned : representedValue move oldPath s = some t) :
    representedFinalData move certificateRest oldPath s saved suffix =
      { certificate := certificateRest, source := saved.reverse ++ treeCode t ++ suffix } := by
  have path := PositionedRotationMachine.remainingPath_nil_of_source_success
    move.direction (move.position ++ oldPath) s t returned
  simp only [representedFinalData,
    representedSource_of_some move oldPath s t saved suffix returned, path]

@[simp] theorem positionData_entryData (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) :
    positionData (entryData raw path source saved scratch pending) =
      { source := source, saved := saved, scratch := scratch, pending := pending, path := path } := rfl

@[simp] theorem positionData_parsedData (move : RotationMove) (rest : Word) (D : LocalData) :
    positionData (parsedData move rest D) =
      { positionData D with path := move.position ++ D.path } := rfl

@[simp] theorem position_reset_reset (regs : Registers R) :
    PositionedRotationMachine.reset (reset regs) = reset regs := rfl

omit [DecidableEq K] in
@[simp] theorem positionContext_parsedData (move : RotationMove) (rest : Word)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    positionContext (parsedData move rest D) ctx =
      positionContext { certificate := rest } ctx := rfl

omit [DecidableEq K] in
/-- Transport a complete Position segment while retaining both parser stores literally. -/
theorem positionCfg_setPositionData
    (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (E : PositionedRotationMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    positionCfg (PositionedRotationMachine.cfg label regs E (positionContext D ctx)) =
      cfg (label.map positionLabelEquiv) regs (setPositionData D E) ctx := by
  change positionCfg (positionView label regs (setPositionData D E) ctx) = _
  exact positionCfg_view label regs (setPositionData D E) ctx

/-! ### The actual parser segment and its paid complete handoff -/

theorem move_start_source_localRun (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (MoveParserMachine.fullSteps raw)
      (entry regs raw path source saved scratch pending ctx)
      (moveCfg (MoveParserMachine.resultCfg (moveRegisterEquiv.symm regs) raw path
        (moveContext (entryData raw path source saved scratch pending) ctx) (parseMoveRun raw).1)) := by
  let D := entryData raw path source saved scratch pending
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
    fun _ => .halt
  have canonical :
      (MoveParserMachine.next localCaller)^[MoveParserMachine.fullSteps raw]
        (some (MoveParserMachine.entry (moveRegisterEquiv.symm regs) raw path (moveContext D ctx))) =
      some (MoveParserMachine.phaseResult .start (moveRegisterEquiv.symm regs) raw [] path
        (moveContext D ctx)) :=
    MoveParserMachine.phase_iterate localCaller .start raw [] path
      (moveRegisterEquiv.symm regs) (moveContext D ctx)
  have observed := MoveParserMachine.run_source localCaller raw path
    (moveRegisterEquiv.symm regs) (moveContext D ctx)
  have same := Option.some.inj (canonical.symm.trans observed)
  have run := move_phase_transport caller .start D regs ctx
  change LocalRun caller (MoveParserMachine.fullSteps raw)
    (entry regs raw path source saved scratch pending ctx)
    (moveCfg (MoveParserMachine.phaseResult .start (moveRegisterEquiv.symm regs) raw [] path
      (moveContext D ctx))) at run
  rw [same] at run
  exact run

theorem parse_failure_localRun (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    LocalRun caller (MoveParserMachine.fullSteps raw)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (entryData raw path source saved scratch pending) ctx) := by
  have run := move_start_source_localRun caller raw path source saved scratch pending regs ctx
  rw [failed] at run
  change LocalRun caller _ _
    (moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
      (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
      (entryData raw path source saved scratch pending) ctx)) at run
  rw [moveCfg_view] at run
  simpa only [Option.map_some, moveLabelEquiv_result, moveRegisterEquiv_reset,
    Equiv.apply_symm_apply] using run

theorem parse_success_localRun (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    LocalRun caller (MoveParserMachine.fullSteps raw)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (dispatchLabel (.success move.direction))) (resetMove regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have run := move_start_source_localRun caller raw path source saved scratch pending regs ctx
  rw [parsed] at run
  change LocalRun caller _ _
    (moveCfg (moveView (some (MoveParserMachine.resultLabel (.success move.direction)))
      (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
      (parsedData move rest (entryData raw path source saved scratch pending)) ctx)) at run
  rw [moveCfg_view] at run
  simpa only [Option.map_some, moveLabelEquiv_result, moveRegisterEquiv_reset,
    Equiv.apply_symm_apply] using run

theorem run_of_none_localRun (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    LocalRun caller (MoveParserMachine.fullSteps raw + 1)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData raw path source saved scratch pending) ctx) := by
  have parsed := parse_failure_localRun caller raw path source saved scratch pending regs ctx failed
  have paid := dispatch_localRun caller .failure
    (entryData raw path source saved scratch pending) (resetMove regs) ctx
  simpa only [dispatchTarget, reset_resetMove] using LocalRun.trans caller parsed paid

theorem paid_position_entry_localRun (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    LocalRun caller (MoveParserMachine.fullSteps raw + 1)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (positionLabel (.seek move.direction))) (reset regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have first := parse_success_localRun caller raw move rest path source saved scratch pending regs ctx parsed
  have paid := dispatch_localRun caller (.success move.direction)
    (parsedData move rest (entryData raw path source saved scratch pending)) (resetMove regs) ctx
  simpa only [dispatchTarget, reset_resetMove] using LocalRun.trans caller first paid

theorem paid_position_code_localRun (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * move.position.length + 4)
      (entry regs (moveCode move ++ rest) path source saved scratch pending ctx)
      (cfg (some (positionLabel (.seek move.direction))) (reset regs)
        { certificate := rest, path := move.position ++ path,
          source := source, saved := saved, scratch := scratch, pending := pending } ctx) := by
  have run := paid_position_entry_localRun caller (moveCode move ++ rest) move rest
    path source saved scratch pending regs ctx (congrArg Prod.fst (parseMoveRun_code move rest))
  simpa only [MoveParserMachine.fullSteps_code, show 2 * move.position.length + 3 + 1 =
      2 * move.position.length + 4 by omega, parsedData, entryData] using run

theorem parse_failure_boundary (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    (next caller)^[MoveParserMachine.fullSteps raw]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (entryData raw path source saved scratch pending) ctx) :=
  LocalRun.iterate caller (parse_failure_localRun caller raw path source saved scratch pending regs ctx failed)

theorem parse_success_boundary (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[2 * move.position.length + 3]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (dispatchLabel (.success move.direction))) (resetMove regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have run := LocalRun.iterate caller
    (parse_success_localRun caller raw move rest path source saved scratch pending regs ctx parsed)
  simpa only [MoveParserMachine.fullSteps_of_some raw move rest parsed] using run

theorem paid_position_entry (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[MoveParserMachine.fullSteps raw + 1]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (positionLabel (.seek move.direction))) (reset regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) :=
  LocalRun.iterate caller
    (paid_position_entry_localRun caller raw move rest path source saved scratch pending regs ctx parsed)

/-! ### Actual composite clocks, first-result observations and typed timing -/

def runSteps (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) : Nat :=
  phaseSteps (movePhase .start) (entryData raw path source saved scratch pending)

def runResult (regs : Registers R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  phaseResult (movePhase .start) regs (entryData raw path source saved scratch pending) ctx

/-- A first live result requires every actual strict earlier state to be owned. -/
def FirstResult (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (result : FinalResult) : Prop :=
  ∃ n reached,
    (next caller)^[n] (some start) = some reached ∧
    reached.l = some (resultLabel result) ∧
    ∀ j, j < n → ∃ before,
      (next caller)^[j] (some start) = some before ∧ Owned before.l

theorem firstResult_iff_phaseResult (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (result : FinalResult) :
    FirstResult caller (cfg (some (phaseLabel q)) regs D ctx) result ↔
      (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel result) := by
  constructor
  · rintro ⟨n, reached, executed, label, earlier⟩
    have external : ¬ Owned reached.l := by
      rw [label]
      exact not_owned_result result
    obtain ⟨_, same⟩ := first_return_unique caller q D regs ctx n reached executed external earlier
    rw [same] at label
    exact label
  · intro label
    obtain ⟨_, earlier⟩ := phase_first_return caller q D regs ctx
    exact ⟨phaseSteps q D, phaseResult q regs D ctx,
      phase_iterate caller q D regs ctx, label, earlier⟩

theorem first_result_complete (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (result : FinalResult)
    (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (label : reached.l = some (resultLabel result))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j] (some (cfg (some (phaseLabel q)) regs D ctx)) = some before ∧ Owned before.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx := by
  apply first_return_unique caller q D regs ctx n reached executed
  · rw [label]
    exact not_owned_result result
  · exact earlier

theorem run_firstResult_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (result : FinalResult) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) result ↔
      (runResult (Λ := Λ) regs raw path source saved scratch pending ctx).l =
        some (resultLabel result) :=
  firstResult_iff_phaseResult caller (movePhase .start)
    (entryData raw path source saved scratch pending) regs ctx result

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

def runInTimeExact (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (runSteps raw path source saved scratch pending) :=
  phaseInTime caller (movePhase .start)
    (entryData raw path source saved scratch pending) regs ctx

def cfgInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start))
      (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := cfg_iterate caller start
  steps_le_m := Nat.le_refl _

theorem run_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    (next caller)^[MoveParserMachine.fullSteps raw + 1]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData raw path source saved scratch pending) ctx) :=
  LocalRun.iterate caller (run_of_none_localRun caller raw path source saved scratch pending regs ctx failed)

include caller in
theorem run_none_data (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 ∧
      runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
        cfg (some (resultLabel parseFailure)) (reset regs)
          (entryData raw path source saved scratch pending) ctx :=
  LocalRun.phase_endpoint caller (q := movePhase .start)
    (run_of_none_localRun caller raw path source saved scratch pending regs ctx failed)

theorem runSteps_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (failed : (parseMoveRun raw).1 = none) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 := by
  let emptyCaller : External Unit → Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  exact (run_none_data emptyCaller raw path source saved scratch pending
    ((none, (none, none)), ()) (fun _ => []) failed).1

include caller in
theorem runResult_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
      cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData raw path source saved scratch pending) ctx :=
  (run_none_data caller raw path source saved scratch pending regs ctx failed).2

theorem run_of_some_localRun (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    LocalRun caller (MoveParserMachine.fullSteps raw + 1 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        (positionData (parsedData move rest (entryData raw path source saved scratch pending))))
      (entry regs raw path source saved scratch pending ctx)
      (phaseResult (positionPhase (.seek move.direction)) regs
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have first := paid_position_entry_localRun caller raw move rest path source saved scratch pending regs ctx parsed
  have last := position_phase_localRun caller (.seek move.direction)
    (parsedData move rest (entryData raw path source saved scratch pending)) (reset regs) ctx
  simpa only [phaseResult_reset] using LocalRun.trans caller first last

include caller in
theorem run_some_data (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 +
        PositionedRotationMachine.phaseSteps (.seek move.direction)
          (positionData (parsedData move rest (entryData raw path source saved scratch pending))) ∧
      runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
        phaseResult (positionPhase (.seek move.direction)) regs
          (parsedData move rest (entryData raw path source saved scratch pending)) ctx :=
  LocalRun.phase_endpoint caller (q := movePhase .start)
    (run_of_some_localRun caller raw move rest path source saved scratch pending regs ctx parsed)

theorem runSteps_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        { source := source, saved := saved, scratch := scratch, pending := pending,
          path := move.position ++ path } := by
  let emptyCaller : External Unit → Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  exact (run_some_data emptyCaller raw move rest path source saved scratch pending
    ((none, (none, none)), ()) (fun _ => []) parsed).1

include caller in
theorem runResult_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
      phaseResult (positionPhase (.seek move.direction)) regs
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx :=
  (run_some_data caller raw move rest path source saved scratch pending regs ctx parsed).2

theorem run_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[MoveParserMachine.fullSteps raw + 1 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        (positionData (parsedData move rest (entryData raw path source saved scratch pending)))]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (phaseResult (positionPhase (.seek move.direction)) regs
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) :=
  LocalRun.iterate caller
    (run_of_some_localRun caller raw move rest path source saved scratch pending regs ctx parsed)

theorem run_code (move : RotationMove) (rest : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * move.position.length + 4 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        { source := source, saved := saved, scratch := scratch, pending := pending,
          path := move.position ++ path }]
      (some (entry regs (moveCode move ++ rest) path source saved scratch pending ctx)) =
      some (phaseResult (positionPhase (.seek move.direction)) regs
        { certificate := rest, path := move.position ++ path,
          source := source, saved := saved, scratch := scratch, pending := pending } ctx) := by
  have run := run_of_some caller (moveCode move ++ rest) move rest path source saved scratch pending
    regs ctx (congrArg Prod.fst (parseMoveRun_code move rest))
  simpa only [MoveParserMachine.fullSteps_code, show 2 * move.position.length + 3 + 1 =
    2 * move.position.length + 4 by omega, positionData, parsedData, entryData] using run

include caller in
theorem run_source (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    match (parseMoveRun raw).1 with
    | none =>
        runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 ∧
        runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
          cfg (some (resultLabel parseFailure)) (reset regs)
            (entryData raw path source saved scratch pending) ctx
    | some (move, rest) =>
        runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 +
          PositionedRotationMachine.phaseSteps (.seek move.direction)
            (positionData (parsedData move rest (entryData raw path source saved scratch pending))) ∧
        runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
          phaseResult (positionPhase (.seek move.direction)) regs
            (parsedData move rest (entryData raw path source saved scratch pending)) ctx := by
  cases parsed : (parseMoveRun raw).1 with
  | none => exact run_none_data caller raw path source saved scratch pending regs ctx parsed
  | some pair =>
      rcases pair with ⟨move, rest⟩
      exact run_some_data caller raw move rest path source saved scratch pending regs ctx parsed

/-- The source observation selects the actual complete joined iteration, including its paid dispatch. -/
theorem run_source_iterate (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    match (parseMoveRun raw).1 with
    | none =>
        (next caller)^[MoveParserMachine.fullSteps raw + 1]
          (some (entry regs raw path source saved scratch pending ctx)) =
          some (cfg (some (resultLabel parseFailure)) (reset regs)
            (entryData raw path source saved scratch pending) ctx)
    | some (move, rest) =>
        (next caller)^[MoveParserMachine.fullSteps raw + 1 +
          PositionedRotationMachine.phaseSteps (.seek move.direction)
            (positionData (parsedData move rest (entryData raw path source saved scratch pending)))]
          (some (entry regs raw path source saved scratch pending ctx)) =
          some (phaseResult (positionPhase (.seek move.direction)) regs
            (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  cases parsed : (parseMoveRun raw).1 with
  | none => exact run_of_none caller raw path source saved scratch pending regs ctx parsed
  | some pair =>
      rcases pair with ⟨move, rest⟩
      exact run_of_some caller raw move rest path source saved scratch pending regs ctx parsed

omit [DecidableEq K] in
theorem position_result_label_iff (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (r : PositionedRotationMachine.Result) :
    (phaseResult (Λ := Λ) (positionPhase q) regs D ctx).l = some (resultLabel (.inr r)) ↔
      (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) q regs
        (positionData D) (positionContext D ctx)).l = some (PositionedRotationMachine.resultLabel r) := by
  simp only [phaseResult, positionPhase, evaluate, evaluatePosition, cfg, resultLabel,
    PositionedRotationMachine.phaseResult, PositionedRotationMachine.cfg,
    PositionedRotationMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq]

theorem first_parseFailure_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) parseFailure ↔
      (parseMoveRun raw).1 = none := by
  rw [run_firstResult_iff]
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runResult_of_none caller raw path source saved scratch pending regs ctx parsed]
      simp [cfg]
  | some pair =>
      rcases pair with ⟨move, rest⟩
      rw [runResult_of_some caller raw move rest path source saved scratch pending regs ctx parsed]
      simp [phaseResult, positionPhase, evaluate, evaluatePosition, cfg, resultLabel, parseFailure]

theorem first_rotation_result_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (r : PositionedRotationMachine.Result) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) (.inr r) ↔
      ∃ move rest, (parseMoveRun raw).1 = some (move, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek move.direction)
          regs
          { source := source, saved := saved, scratch := scratch, pending := pending,
            path := move.position ++ path }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel r) := by
  constructor
  · intro first
    have returned := (run_firstResult_iff caller raw path source saved scratch pending regs ctx (.inr r)).mp first
    cases parsed : (parseMoveRun raw).1 with
    | none =>
        rw [runResult_of_none caller raw path source saved scratch pending regs ctx parsed] at returned
        simp [cfg, resultLabel, parseFailure] at returned
    | some pair =>
        rcases pair with ⟨move, rest⟩
        rw [runResult_of_some caller raw move rest path source saved scratch pending regs ctx parsed] at returned
        refine ⟨move, rest, rfl, ?_⟩
        exact (position_result_label_iff (.seek move.direction)
          (parsedData move rest (entryData raw path source saved scratch pending)) regs ctx r).mp returned
  · rintro ⟨move, rest, parsed, returned⟩
    apply (run_firstResult_iff caller raw path source saved scratch pending regs ctx (.inr r)).mpr
    rw [runResult_of_some caller raw move rest path source saved scratch pending regs ctx parsed]
    exact (position_result_label_iff (.seek move.direction)
      (parsedData move rest (entryData raw path source saved scratch pending)) regs ctx r).mpr returned

theorem first_rotationFailure_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) rotationFailure ↔
      ∃ move rest, (parseMoveRun raw).1 = some (move, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek move.direction)
          regs
          { source := source, saved := saved, scratch := scratch, pending := pending,
            path := move.position ++ path }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .failure) :=
  first_rotation_result_iff caller raw path source saved scratch pending regs ctx .failure

theorem first_success_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) success ↔
      ∃ move rest, (parseMoveRun raw).1 = some (move, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek move.direction)
          regs
          { source := source, saved := saved, scratch := scratch, pending := pending,
            path := move.position ++ path }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .success) :=
  first_rotation_result_iff caller raw path source saved scratch pending regs ctx .success

/-! ### Complete Position segments on the same physical parser stores -/

theorem position_segment_localRun
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (D : LocalData) (ctx : ∀ k, List (Γ k))
    {n : Nat} {beforeLabel afterLabel : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ))}
    {beforeRegs afterRegs : Registers R} {beforeData afterData : PositionedRotationMachine.LocalData}
    (run : PositionedRotationMachine.LocalRun localCaller n
      (PositionedRotationMachine.cfg beforeLabel beforeRegs beforeData (positionContext D ctx))
      (PositionedRotationMachine.cfg afterLabel afterRegs afterData (positionContext D ctx))) :
    LocalRun caller n
      (cfg (beforeLabel.map positionLabelEquiv) beforeRegs (setPositionData D beforeData) ctx)
      (cfg (afterLabel.map positionLabelEquiv) afterRegs (setPositionData D afterData) ctx) := by
  have transported := position_localRun_transport caller localCaller run
  rw [positionCfg_setPositionData beforeLabel beforeRegs D beforeData ctx,
    positionCfg_setPositionData afterLabel afterRegs D afterData ctx] at transported
  exact transported

/-- The represented suffix is the actual parsed segment, paid dispatch and Position LocalRun. -/
theorem run_code_represented_localRun (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (representedSteps move oldPath s saved)
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R :=
    fun _ => .halt
  have positionRun := PositionedRotationMachine.run_code_localRun localCaller move.direction
    (move.position ++ oldPath) s saved suffix (reset regs) (positionContext D ctx)
  have last := position_segment_localRun caller localCaller D ctx positionRun
  have first := paid_position_code_localRun caller move certificateRest oldPath
    (treeCode s ++ suffix) saved [] [] regs ctx
  have joined := LocalRun.trans caller first last
  cases actual : (applyMoveRun ⟨move.direction, move.position ++ oldPath⟩ s).1 <;>
    simpa [representedSteps, representedFinalData, representedSource, representedResult,
      representedValue, physicalMove, PositionedRotationMachine.sourceResult, success, rotationFailure,
      D, setPositionData, Option.map_some, positionLabelEquiv_phase, positionLabelEquiv_result,
      reset, PositionedRotationMachine.reset, actual, Nat.add_assoc] using joined

include caller in
theorem represented_run_data (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] =
        representedSteps move oldPath s saved ∧
      runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
        (treeCode s ++ suffix) saved [] [] ctx =
        cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
          (representedFinalData move certificateRest oldPath s saved suffix) ctx :=
  LocalRun.phase_endpoint caller (q := movePhase .start)
    (run_code_represented_localRun caller move certificateRest oldPath s saved suffix regs ctx)

include caller in
/-- Both represented outcomes have the same actual source-store length, including the restored saved prefix. -/
theorem represented_run_source_length (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ((runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
      (treeCode s ++ suffix) saved [] [] ctx).stk (.inl .source)).length =
      saved.length + 2 * s.numNodes + 1 + suffix.length := by
  rw [(represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  exact representedFinalData_source_length move certificateRest oldPath s saved suffix

theorem run_code_represented (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedSteps move oldPath s saved]
      (some (entry regs (moveCode move ++ certificateRest) oldPath
        (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx) :=
  LocalRun.iterate caller
    (run_code_represented_localRun caller move certificateRest oldPath s saved suffix regs ctx)

def representedInTime (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (some (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx))
      (representedSteps move oldPath s saved) where
  steps := representedSteps move oldPath s saved
  evals_in_steps := run_code_represented caller move certificateRest oldPath s saved suffix regs ctx
  steps_le_m := Nat.le_refl _

theorem represented_first_success_iff (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      success ↔ ∃ t, representedValue move oldPath s = some t := by
  rw [run_firstResult_iff,
    (represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  simpa only [cfg, resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] using
    representedResult_success_iff move oldPath s

theorem represented_first_failure_iff (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      rotationFailure ↔ representedValue move oldPath s = none := by
  rw [run_firstResult_iff,
    (represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  simpa only [cfg, resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] using
    representedResult_failure_iff move oldPath s

include caller in
theorem represented_complete_output_success_iff (move : RotationMove)
    (certificateRest outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
        (treeCode s ++ suffix) saved [] [] ctx =
      cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx ↔
      representedValue move oldPath s = some t ∧
        certificateRest = outputCertificate ∧ suffix = outputSuffix := by
  rw [(represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  constructor
  · intro endpoint
    have label := congrArg (fun c : Cfg Γ Λ R => c.l) endpoint
    have certificate := congrArg (fun c : Cfg Γ Λ R => (dataOfCfg c).certificate) endpoint
    have source := congrArg (fun c : Cfg Γ Λ R => (dataOfCfg c).source) endpoint
    have certificateEq : certificateRest = outputCertificate := certificate
    have sourceEq : representedSource move oldPath s saved suffix =
        saved.reverse ++ treeCode t ++ outputSuffix := source
    cases actual : representedValue move oldPath s with
    | none =>
        simp [representedResult, actual, cfg, resultLabel, success, rotationFailure] at label
    | some u =>
        have unique := representedSource_success_injective move oldPath s u t
          saved suffix outputSuffix actual sourceEq
        exact ⟨congrArg some unique.1, certificateEq, unique.2⟩
  · rintro ⟨returned, rfl, rfl⟩
    rw [representedResult_of_some move oldPath s t returned,
      representedFinalData_of_some move certificateRest oldPath s t saved suffix returned]

theorem represented_success_localRun_iff (move : RotationMove)
    (certificateRest outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    LocalRun caller n
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx) ↔
      representedValue move oldPath s = some t ∧ certificateRest = outputCertificate ∧
        suffix = outputSuffix ∧ n = representedSteps move oldPath s saved := by
  constructor
  · intro run
    have endpoint := LocalRun.phase_endpoint caller (q := movePhase .start) run
    have output := (represented_complete_output_success_iff caller move certificateRest outputCertificate
      oldPath s t saved suffix outputSuffix regs ctx).mp endpoint.2
    exact ⟨output.1, output.2.1, output.2.2,
      endpoint.1.symm.trans (represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).1⟩
  · rintro ⟨returned, rfl, rfl, rfl⟩
    have run := run_code_represented_localRun caller move certificateRest oldPath s saved suffix regs ctx
    rw [representedResult_of_some move oldPath s t returned,
      representedFinalData_of_some move certificateRest oldPath s t saved suffix returned] at run
    exact run

theorem represented_first_success_complete (move : RotationMove)
    (certificateRest outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (executed : (next caller)^[n]
      (some (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j]
        (some (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
        some before ∧ Owned before.l) :
    representedValue move oldPath s = some t ∧ certificateRest = outputCertificate ∧
      suffix = outputSuffix ∧ n = representedSteps move oldPath s saved :=
  (represented_success_localRun_iff caller move certificateRest outputCertificate oldPath s t
    saved suffix outputSuffix regs ctx n).mp (LocalRun.of_iterate caller executed earlier)

include caller in
theorem represented_success_semantics (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (endpoint : runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
      (treeCode s ++ suffix) saved [] [] ctx =
      cfg (some (resultLabel success)) (reset regs)
        { certificate := certificateRest, source := saved.reverse ++ treeCode t ++ suffix } ctx) :
    Trees.Rotations.applyMove? (physicalMove move oldPath) s = some t ∧
      t.numNodes = s.numNodes ∧
      (applyMoveRun (physicalMove move oldPath) s).2 = 3 * (move.position ++ oldPath).length + 5 ∧
      (saved.reverse ++ treeCode t ++ suffix).length =
        saved.length + 2 * s.numNodes + 1 + suffix.length := by
  have returned := ((represented_complete_output_success_iff caller move certificateRest certificateRest
    oldPath s t saved suffix suffix regs ctx).mp endpoint).1
  have nodes := representedValue_numNodes move oldPath s t returned
  refine ⟨(representedValue_eq_applyMove move oldPath s).symm.trans returned,
    nodes, source_application_cost_of_some move oldPath s t returned, ?_⟩
  simp only [List.length_append, List.length_reverse, treeCode_length, nodes, Nat.add_assoc]

/-! ### Linear bounds retain the same actual exact execution count -/

theorem runSteps_le_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runSteps raw path source saved scratch pending ≤
      3 * source.length + saved.length + scratch.length + pending.length +
        3 * move.position.length + path.length + 9 := by
  rw [runSteps_of_some raw move rest path source saved scratch pending parsed,
    MoveParserMachine.fullSteps_of_some raw move rest parsed]
  have bound := PositionedRotationMachine.phaseSteps_le_countdown (.seek move.direction)
    { source := source, saved := saved, scratch := scratch, pending := pending,
      path := move.position ++ path }
  simp only [PositionedRotationMachine.countdown, List.length_append] at bound
  omega

theorem runSteps_le (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) :
    runSteps raw path source saved scratch pending ≤
      3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3 := by
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runSteps_of_none raw path source saved scratch pending parsed]
      have bound := MoveParserMachine.fullSteps_le raw
      omega
  | some pair =>
      rcases pair with ⟨move, rest⟩
      have bound := runSteps_le_of_some raw move rest path source saved scratch pending parsed
      have length := parseMoveRun_consumed_length raw move rest parsed
      omega

def runInLinearTime (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (runInTimeExact caller raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le raw path source saved scratch pending

def parsedRunInLinearTime (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (3 * source.length + saved.length + scratch.length + pending.length +
        3 * move.position.length + path.length + 9) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (runInTimeExact caller raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le_of_some raw move rest path source saved scratch pending parsed

/-! ### Component timing retains the real internal reset boundary -/

def movePhaseInTime (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel q)) regs D ctx)
      (some (cfg (some (dispatchLabel (moveFinish q D).result)) (resetMove regs)
        (moveFinish q D).data ctx))
      (MoveParserMachine.phaseSteps q D.certificate D.moveReverse) where
  steps := MoveParserMachine.phaseSteps q D.certificate D.moveReverse
  evals_in_steps := LocalRun.iterate caller (move_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

def dispatchInTime (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (dispatchLabel r)) regs D ctx)
      (some (cfg (some (dispatchTarget r)) (reset regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := LocalRun.iterate caller (dispatch_localRun caller r D regs ctx)
  steps_le_m := Nat.le_refl _

def positionPhaseInTime (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (positionLabel q)) regs D ctx)
      (some (phaseResult (positionPhase q) regs D ctx))
      (PositionedRotationMachine.phaseSteps q (positionData D)) where
  steps := PositionedRotationMachine.phaseSteps q (positionData D)
  evals_in_steps := LocalRun.iterate caller (position_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

/-! ### Complete raw-word behavior after one successful parse -/

/-- Raw Position failure restores its tree input after the certificate has actually been consumed. -/
theorem run_raw (move : RotationMove) (certificateRest : Word) (oldPath : List Branch)
    (source : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ result output rest,
      LocalRun caller
        (2 * move.position.length + 4 +
          PositionedRotationMachine.runSteps move.direction source (move.position ++ oldPath))
        (entry regs (moveCode move ++ certificateRest) oldPath source [] [] [] ctx)
        (cfg (some (resultLabel (.inr result))) (reset regs)
          { certificate := certificateRest, source := output, path := rest } ctx) ∧
      output.length = source.length ∧
      (∃ consumed, move.position ++ oldPath = consumed ++ rest) ∧
      (result = .failure → output = source) ∧ (result = .success → rest = []) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  obtain ⟨result, output, rest, run, length, path, failed, succeeded⟩ :=
    PositionedRotationMachine.run_raw localCaller move.direction source
      (move.position ++ oldPath) (reset regs) (positionContext D ctx)
  have transported := position_segment_localRun caller localCaller D ctx run
  have paid := paid_position_code_localRun caller move certificateRest oldPath source [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  refine ⟨result, output, rest, ?_, length, path, failed, succeeded⟩
  simpa only [D, setPositionData, Option.map_some, positionLabelEquiv_phase,
    positionLabelEquiv_result, position_reset_reset] using joined

include caller in
/-- Canonical raw endpoints retain length and the physically unvisited path suffix. -/
theorem run_raw_data (move : RotationMove) (certificateRest : Word) (oldPath : List Branch)
    (source : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ result output rest,
      runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath source [] [] [] ctx =
        cfg (some (resultLabel (.inr result))) (reset regs)
          { certificate := certificateRest, source := output, path := rest } ctx ∧
      output.length = source.length ∧
      (∃ consumed, move.position ++ oldPath = consumed ++ rest) ∧
      (result = .failure → output = source) ∧ (result = .success → rest = []) := by
  obtain ⟨result, output, rest, run, length, path, failed, succeeded⟩ :=
    run_raw caller move certificateRest oldPath source regs ctx
  exact ⟨result, output, rest, (LocalRun.phase_endpoint caller (q := movePhase .start) run).2,
    length, path, failed, succeeded⟩

/-! ### Root recognition on arbitrary literal suffixes -/

theorem root_left_pattern_localRun (A : BinaryTree Unit) (suffix saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 9 + saved.length)
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) []
        (nodeTag :: (treeCode A ++ nodeTag :: suffix)) saved [] [] ctx)
      (cfg (some (resultLabel success)) (reset regs)
        { certificate := certificateRest,
          source := saved.reverse ++ [nodeTag, nodeTag] ++ treeCode A ++ suffix } ctx) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.root_left_pattern_localRun localCaller A suffix saved
    (reset regs) (positionContext D ctx)
  have transported := position_segment_localRun caller localCaller D ctx run
  have paid := paid_position_code_localRun caller ⟨.left, []⟩ certificateRest []
    (nodeTag :: (treeCode A ++ nodeTag :: suffix)) saved [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;>
    simp [D, setPositionData, success, Nat.add_assoc]; omega

theorem root_right_pattern_localRun (A : BinaryTree Unit) (suffix saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 8 + saved.length)
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) []
        (nodeTag :: nodeTag :: (treeCode A ++ suffix)) saved [] [] ctx)
      (cfg (some (resultLabel success)) (reset regs)
        { certificate := certificateRest,
          source := saved.reverse ++ [nodeTag] ++ treeCode A ++ nodeTag :: suffix } ctx) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.root_right_pattern_localRun localCaller A suffix saved
    (reset regs) (positionContext D ctx)
  have transported := position_segment_localRun caller localCaller D ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (nodeTag :: nodeTag :: (treeCode A ++ suffix)) saved [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;>
    simp [D, setPositionData, success, Nat.add_assoc]; omega

/-- A first success recognizes only the required root prefix, including malformed suffixes. -/
theorem root_left_first_success_iff (source saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] source saved [] [] ctx) success ↔
      ∃ A : BinaryTree Unit, ∃ suffix : Word,
        source = nodeTag :: (treeCode A ++ nodeTag :: suffix) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  rw [run_firstResult_iff, runResult_of_some caller _ ⟨.left, []⟩ certificateRest
    [] source saved [] [] regs ctx (congrArg Prod.fst (parseMoveRun_code ⟨.left, []⟩ certificateRest))]
  change (phaseResult (positionPhase (.seek .left)) regs
    { certificate := certificateRest, source := source, saved := saved } ctx).l =
      some (resultLabel (.inr .success)) ↔ _
  rw [position_result_label_iff]
  exact PositionedRotationMachine.root_left_phaseResult_success_iff localCaller source saved regs
    (positionContext { certificate := certificateRest } ctx)

theorem root_right_first_success_iff (source saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] source saved [] [] ctx) success ↔
      ∃ A : BinaryTree Unit, ∃ suffix : Word,
        source = nodeTag :: nodeTag :: (treeCode A ++ suffix) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  rw [run_firstResult_iff, runResult_of_some caller _ ⟨.right, []⟩ certificateRest
    [] source saved [] [] regs ctx (congrArg Prod.fst (parseMoveRun_code ⟨.right, []⟩ certificateRest))]
  change (phaseResult (positionPhase (.seek .right)) regs
    { certificate := certificateRest, source := source, saved := saved } ctx).l =
      some (resultLabel (.inr .success)) ↔ _
  rw [position_result_label_iff]
  exact PositionedRotationMachine.root_right_phaseResult_success_iff localCaller source saved regs
    (positionContext { certificate := certificateRest } ctx)

/-! ### An arbitrary certificate's complete represented first-success converse -/

include caller in
theorem represented_output_success_iff (raw outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx =
      cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx ↔
      ∃ move, (parseMoveRun raw).1 = some (move, outputCertificate) ∧
        representedValue move oldPath s = some t ∧ suffix = outputSuffix := by
  constructor
  · intro endpoint
    cases parsed : (parseMoveRun raw).1 with
    | none =>
        rw [runResult_of_none caller raw oldPath (treeCode s ++ suffix) saved [] [] regs ctx parsed] at endpoint
        have label := congrArg (fun c : Cfg Γ Λ R => c.l) endpoint
        cases label
    | some pair =>
        rcases pair with ⟨move, rest⟩
        have word := (parseMoveRun_iff raw move rest).mp parsed
        rw [word] at endpoint
        obtain ⟨returned, restEq, suffixEq⟩ :=
          (represented_complete_output_success_iff caller move rest outputCertificate oldPath
            s t saved suffix outputSuffix regs ctx).mp endpoint
        exact ⟨move, by simp only [restEq], returned, suffixEq⟩
  · rintro ⟨move, parsed, returned, suffixEq⟩
    rw [(parseMoveRun_iff raw move outputCertificate).mp parsed]
    exact (represented_complete_output_success_iff caller move outputCertificate outputCertificate
      oldPath s t saved suffix outputSuffix regs ctx).mpr ⟨returned, rfl, suffixEq⟩

theorem represented_raw_first_success_iff (raw : Word) (oldPath : List Branch)
    (s : BinaryTree Unit) (saved suffix : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx) success ↔
      ∃ move rest t, (parseMoveRun raw).1 = some (move, rest) ∧
        representedValue move oldPath s = some t := by
  constructor
  · intro first
    obtain ⟨move, rest, parsed, _⟩ :=
      (first_success_iff caller raw oldPath (treeCode s ++ suffix) saved [] [] regs ctx).mp first
    have word := (parseMoveRun_iff raw move rest).mp parsed
    rw [word] at first
    obtain ⟨t, returned⟩ :=
      (represented_first_success_iff caller move rest oldPath s saved suffix regs ctx).mp first
    exact ⟨move, rest, t, parsed, returned⟩
  · rintro ⟨move, rest, t, parsed, returned⟩
    rw [(parseMoveRun_iff raw move rest).mp parsed]
    exact (represented_first_success_iff caller move rest oldPath s saved suffix regs ctx).mpr
      ⟨t, returned⟩

theorem represented_raw_first_success_complete (raw outputCertificate : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (executed : (next caller)^[n]
      (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j] (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
        some before ∧ Owned before.l) :
    ∃ move, (parseMoveRun raw).1 = some (move, outputCertificate) ∧
      representedValue move oldPath s = some t ∧ suffix = outputSuffix ∧
      n = representedSteps move oldPath s saved := by
  have run := LocalRun.of_iterate caller executed earlier
  have endpoint := LocalRun.phase_endpoint caller (q := movePhase .start) run
  obtain ⟨move, parsed, returned, suffixEq⟩ :=
    (represented_output_success_iff caller raw outputCertificate oldPath s t saved suffix outputSuffix regs ctx).mp
      endpoint.2
  refine ⟨move, parsed, returned, suffixEq, ?_⟩
  have word := (parseMoveRun_iff raw move outputCertificate).mp parsed
  rw [word] at endpoint
  exact endpoint.1.symm.trans
    (represented_run_data caller move outputCertificate oldPath s saved suffix regs ctx).1

theorem represented_raw_first_success_unique (raw outputCertificate : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (executed : (next caller)^[n]
      (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j] (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
        some before ∧ Owned before.l) :
    ∃ move, (parseMoveRun raw).1 = some (move, outputCertificate) ∧
      representedValue move oldPath s = some t ∧ suffix = outputSuffix ∧
      n = representedSteps move oldPath s saved ∧
      ∀ other otherRest, (parseMoveRun raw).1 = some (other, otherRest) →
        other = move ∧ otherRest = outputCertificate := by
  obtain ⟨move, parsed, returned, suffixEq, count⟩ :=
    represented_raw_first_success_complete caller raw outputCertificate oldPath s t saved suffix
      outputSuffix regs ctx n executed earlier
  exact ⟨move, parsed, returned, suffixEq, count,
    fun other otherRest observed => parsed_prefix_unique raw other move otherRest outputCertificate observed parsed⟩

/-! ### Actual segment composition for later inclusive prefixes -/

theorem prefix_iterate_after_localRun {start middle : Cfg Γ Λ R} {first : Nat}
    (segment : LocalRun caller first start middle) (n : Nat) (after : first ≤ n)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    (next caller)^[n - first] (some middle) = some reached := by
  have split : n = (n - first) + first := by omega
  rw [split, Function.iterate_add_apply, LocalRun.iterate caller segment] at executed
  exact executed


end Resources.RotationCertificate.MoveApplyMachine
