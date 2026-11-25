import Applications.Resources.RotationCertificate.StreamMachine.InitialExecution

/-!
# StreamMachine: CleanExecution
-/

set_option autoImplicit false
set_option warningAsError true

-- BEGIN COMPLETE SOURCE SUFFIX6
namespace Resources.RotationCertificate.StreamMachine

open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ### Pure complete MoveApply observations used by clean Stream induction -/

/-- The seven MoveApply stores at a clean Stream call; fuel and target are in
the caller complement of this component. -/
def moveCleanData (raw source : Word) : MoveApplyMachine.LocalData :=
  MoveApplyMachine.entryData raw [] source [] [] []

private theorem move_evaluation_eq (actual : MoveApplyMachine.Evaluation)
    (result : MoveApplyMachine.FinalResult) (D : MoveApplyMachine.LocalData) (ticks : Nat)
    (label : actual.result = result) (data : actual.data = D) (clock : actual.steps = ticks) :
    actual = ⟨result, D, ticks⟩ := by
  cases actual
  cases label
  cases data
  cases clock
  rfl

/-- Clean source parse failure preserves the complete component input and pays
the real parser clock plus its actual one-step failure dispatch. -/
theorem move_clean_parse_failure (raw source : Word)
    (failed : (parseMoveRun raw).1 = none) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData raw source) =
      ⟨MoveApplyMachine.parseFailure, moveCleanData raw source,
        MoveParserMachine.fullSteps raw + 1⟩ := by
  let caller : MoveApplyMachine.External Unit →
      MoveApplyMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : MoveApplyMachine.Registers Unit := ((none, (none, none)), ())
  have actual := MoveApplyMachine.run_none_data caller raw [] source [] [] [] regs (fun _ => []) failed
  have label := congrArg (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => c.l) actual.2
  have data := congrArg
    (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => MoveApplyMachine.dataOfCfg c) actual.2
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult, MoveApplyMachine.cfg,
    MoveApplyMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at label
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult,
    MoveApplyMachine.dataOfCfg_cfg] at data
  exact move_evaluation_eq _ _ _ _ label data actual.1

/-- A parsed clean raw call returns the actual output and unvisited path, with
all four temporary stacks empty. The output length is preserved even on raw
malformed words; rotation failure restores the source word literally. -/
theorem move_clean_parsed_raw (raw source : Word) (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    ∃ result output path,
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData raw source) =
        ⟨.inr result, { certificate := rest, source := output, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      (∃ consumed, move.position = consumed ++ path) ∧
      (result = .failure → output = source) ∧
      (result = .success → path = []) := by
  let caller : MoveApplyMachine.External Unit →
      MoveApplyMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : MoveApplyMachine.Registers Unit := ((none, (none, none)), ())
  obtain ⟨result, output, path, endpoint, length, suffix, failed, succeeded⟩ :=
    MoveApplyMachine.run_raw_data caller move rest [] source regs (fun _ => [])
  rw [← (parseMoveRun_iff raw move rest).mp parsed] at endpoint
  have label := congrArg (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => c.l) endpoint
  have data := congrArg
    (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => MoveApplyMachine.dataOfCfg c) endpoint
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult, MoveApplyMachine.cfg,
    MoveApplyMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at label
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult,
    MoveApplyMachine.dataOfCfg_cfg] at data
  have clock := MoveApplyMachine.runSteps_of_some raw move rest [] source [] [] [] parsed
  rw [MoveParserMachine.fullSteps_of_some raw move rest parsed] at clock
  simp only [List.append_nil] at clock suffix
  refine ⟨result, output, path, move_evaluation_eq _ _ _ _ label data ?_,
    length, suffix, failed, succeeded⟩
  exact clock

/-- Every clean successful raw application has a literal shorter certificate,
the actual length-preserving output word, and no auxiliary residue. -/
theorem move_clean_success (raw source : Word)
    (returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData raw source)).result = MoveApplyMachine.success) :
    ∃ move rest output,
      (parseMoveRun raw).1 = some (move, rest) ∧
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData raw source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      raw.length = move.position.length + 2 + rest.length ∧
      rest.length < raw.length := by
  obtain ⟨move, rest, parsed, intermediate, certificate, encoded, consumed, two, less⟩ :=
    move_start_success_has_parse (moveCleanData raw source) returned
  obtain ⟨result, output, path, actual, length, suffix, failed, succeeded⟩ :=
    move_clean_parsed_raw raw source move rest parsed
  have isSuccess : result = .success := by
    rw [actual] at returned
    exact Sum.inr.inj returned
  have empty := succeeded isSuccess
  subst result
  subst path
  exact ⟨move, rest, output, parsed, actual, length, consumed, less⟩

/-- Both represented outcomes are the complete existing MoveApply endpoint,
with its real physical clock and without changing the source tariff. -/
theorem move_clean_represented (move : RotationMove) (rest : Word) (s : BinaryTree Unit) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
        (moveCleanData (moveCode move ++ rest) (treeCode s)) =
      ⟨MoveApplyMachine.representedResult move [] s,
        MoveApplyMachine.representedFinalData move rest [] s [] [],
        MoveApplyMachine.representedSteps move [] s []⟩ := by
  let caller : MoveApplyMachine.External Unit →
      MoveApplyMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : MoveApplyMachine.Registers Unit := ((none, (none, none)), ())
  have actual := MoveApplyMachine.represented_run_data caller move rest [] s [] [] regs (fun _ => [])
  simp only [List.append_nil] at actual
  have label := congrArg (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => c.l) actual.2
  have data := congrArg
    (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => MoveApplyMachine.dataOfCfg c) actual.2
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult, MoveApplyMachine.cfg,
    MoveApplyMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at label
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult,
    MoveApplyMachine.dataOfCfg_cfg] at data
  exact move_evaluation_eq _ _ _ _ label data actual.1

/-- The parser-failure branch uses its own shorter bound, not the looser parsed
Position bound that would hide the uniform clean-stream arithmetic. -/
theorem move_clean_steps_of_none (raw source : Word)
    (failed : (parseMoveRun raw).1 = none) :
    (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData raw source)).steps ≤ 2 * raw.length + 2 := by
  rw [move_clean_parse_failure raw source failed]
  have bound := MoveParserMachine.fullSteps_le raw
  dsimp only
  omega

theorem move_clean_steps_of_some (raw source : Word) (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData raw source)).steps ≤
      3 * source.length + 3 * move.position.length + 9 := by
  have bound := MoveApplyMachine.runSteps_le_of_some raw move rest [] source [] [] [] parsed
  change (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
    (moveCleanData raw source)).steps ≤ _ at bound
  simpa only [List.length_nil, Nat.add_zero] using bound

/-- Successful represented application exposes the exact current source tree,
with the complete parser suffix and no physical path or auxiliary residue. -/
theorem move_clean_represented_of_some (move : RotationMove) (rest : Word)
    (s nextTree : BinaryTree Unit)
    (returned : (applyMoveRun move s).1 = some nextTree) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData (moveCode move ++ rest) (treeCode s)) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := treeCode nextTree },
          MoveApplyMachine.representedSteps move [] s []⟩ := by
  have actual : MoveApplyMachine.representedValue move [] s = some nextTree := by
    simpa only [MoveApplyMachine.representedValue, MoveApplyMachine.physicalMove_nil] using returned
  rw [move_clean_represented, MoveApplyMachine.representedResult_of_some move [] s nextTree actual,
    MoveApplyMachine.representedFinalData_of_some move rest [] s nextTree [] [] actual]
  simp only [List.reverse_nil, List.nil_append, List.append_nil]

/-- Failure retains the literal unvisited represented path and restored source;
it consumes the parsed move but does not invoke a later stream activation. -/
theorem move_clean_represented_of_none (move : RotationMove) (rest : Word)
    (s : BinaryTree Unit) (failed : (applyMoveRun move s).1 = none) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData (moveCode move ++ rest) (treeCode s)) =
        ⟨MoveApplyMachine.rotationFailure,
          { certificate := rest, source := treeCode s,
            path := PositionedRotationMachine.remainingPath move.position s },
          MoveApplyMachine.representedSteps move [] s []⟩ := by
  have actual : MoveApplyMachine.representedValue move [] s = none := by
    simpa only [MoveApplyMachine.representedValue, MoveApplyMachine.physicalMove_nil] using failed
  rw [move_clean_represented, MoveApplyMachine.representedResult_of_none move [] s actual]
  simp only [MoveApplyMachine.representedFinalData,
    MoveApplyMachine.representedSource_of_none move [] s [] [] actual,
    List.reverse_nil, List.nil_append, List.append_nil]


/-! ### Clean raw inspection, exact paid branches and complete source endpoints -/

/-- Principal raw input. Registers and external stores remain arbitrary. -/
def cleanData (fuel : Bits) (certificate source target : Word) : LocalData where
  certificate := certificate
  source := source
  fuel := fuel
  target := target

def entry (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel inspectPhase)) regs (cleanData fuel certificate source target) ctx

def runEvaluation (fuel : Bits) (certificate source target : Word) : Evaluation :=
  evaluateInspect (cleanData fuel certificate source target)

def runSteps (fuel : Bits) (certificate source target : Word) : Nat :=
  (runEvaluation fuel certificate source target).steps

def runResult (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  evaluationCfg regs (runEvaluation fuel certificate source target) ctx

omit [DecidableEq K] in
@[simp] theorem remainingSteps_entry (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (entry (Λ := Λ) regs fuel certificate source target ctx) =
      runSteps fuel certificate source target :=
  remainingSteps_phase_cfg inspectPhase (cleanData fuel certificate source target) regs ctx

/-- Literal replacement of just the seven physical MoveApply stores. -/
def liftMoveData (fuel : Bits) (target : Word) (D : MoveApplyMachine.LocalData) : LocalData where
  certificate := D.certificate
  moveReverse := D.moveReverse
  path := D.path
  source := D.source
  saved := D.saved
  scratch := D.scratch
  units := D.pending
  fuel := fuel
  target := target

@[simp] theorem applyData_cleanData (fuel : Bits) (certificate source target : Word) :
    applyData (cleanData fuel certificate source target) = moveCleanData certificate source := rfl

@[simp] theorem setApplyData_cleanData (fuel : Bits) (certificate source target : Word)
    (D : MoveApplyMachine.LocalData) :
    setApplyData (cleanData fuel certificate source target) D = liftMoveData fuel target D := rfl

@[simp] theorem liftMoveData_clean (fuel : Bits) (certificate source target : Word) :
    liftMoveData fuel target { certificate := certificate, source := source } =
      cleanData fuel certificate source target := rfl

@[simp] theorem counterFinish_clean (fuel : Bits) (certificate source target : Word) :
    counterFinish .borrow (cleanData fuel certificate source target) =
      ⟨(Resources.BinaryCounter.FixedWidthMachine.predSpec fuel).1,
        cleanData (Resources.BinaryCounter.FixedWidthMachine.predSpec fuel).2 certificate source target,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel⟩ := by
  simp only [counterFinish, cleanData, List.length_nil, List.replicate_zero,
    List.nil_append, Nat.add_zero]

@[simp] theorem applyFinish_clean (fuel : Bits) (certificate source target : Word) :
    applyFinish (MoveApplyMachine.movePhase .start) (cleanData fuel certificate source target) =
      let actual := MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
        (moveCleanData certificate source)
      ⟨actual.result, liftMoveData fuel target actual.data, actual.steps⟩ := rfl

@[simp] theorem equalityResult_wordResult (source target : Word) :
    equalityResult (TreeEqualityMachine.wordResult source target) = decide (source = target) := by
  by_cases same : source = target
  · simp only [TreeEqualityMachine.wordResult, ite_eq_left same, equalityResult, decide_eq_true same]
  · simp only [TreeEqualityMachine.wordResult, ite_eq_right same, equalityResult, decide_eq_false same]

/-- EOF precedes fuel and pays inspection, the atEnd join and the result join. -/
theorem runEvaluation_nil (fuel : Bits) (source target : Word) :
    runEvaluation fuel [] source target =
      ⟨decide (source = target),
        cleanData fuel [] (source.drop (TreeEqualityMachine.runSteps source target))
          (target.drop (TreeEqualityMachine.runSteps source target)),
        TreeEqualityMachine.runSteps source target + 3⟩ := by
  rw [runEvaluation, evaluateInspect_nil _ rfl]
  simp only [addSteps, evaluateEquality, equalityFinish, cleanData, equalityResult_wordResult]
  congr 1
  omega

/-- A nonempty certificate with no predecessor returns before parsing it. -/
theorem runEvaluation_no_fuel (fuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    runEvaluation fuel certificate source target =
      ⟨false, cleanData fuel certificate source target,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2⟩ := by
  rw [runEvaluation, evaluateInspect_nonempty _ nonempty]
  simp only [evaluateCounter, counterFinish_clean,
    Resources.BinaryCounter.FixedWidthMachine.predSpec_of_none failed,
    FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps]
  congr 1
  omega

/-- Complete early failure after an actual positive predecessor. The supplied
MoveApply endpoint retains every raw residual word and every paid clock. -/
theorem runEvaluation_move_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (result : MoveApplyMachine.FinalResult) (D : MoveApplyMachine.LocalData) (ticks : Nat)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) = ⟨result, D, ticks⟩)
    (failed : result ≠ MoveApplyMachine.success) :
    runEvaluation fuel certificate source target =
      ⟨false, liftMoveData nextFuel target D,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + ticks + 3⟩ := by
  rw [runEvaluation, evaluateInspect_nonempty _ nonempty]
  simp only [evaluateCounter, counterFinish_clean,
    Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some decremented,
    FuelDispatchMachine.exitOfResult, evaluateFuelJoin, evaluateApply, applyFinish_clean, applied]
  cases result with
  | inl token =>
      simp only [evaluateApplyJoin, addSteps]
      congr 1
      omega
  | inr result => cases result with
    | failure =>
        simp only [evaluateApplyJoin, addSteps]
        congr 1
        omega
    | success => exact False.elim (failed rfl)

/-- Successful application pays its literal result join and reinspects the
actual complete returned data; there is no new copy, parser call or reset of words. -/
theorem runEvaluation_move_success (fuel nextFuel : Bits) (certificate source target : Word)
    (D : MoveApplyMachine.LocalData) (ticks : Nat)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) = ⟨MoveApplyMachine.success, D, ticks⟩) :
    runEvaluation fuel certificate source target =
      addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + ticks + 3)
        (evaluateInspect (liftMoveData nextFuel target D)) := by
  rw [runEvaluation, evaluateInspect_nonempty _ nonempty]
  simp only [evaluateCounter, counterFinish_clean,
    Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some decremented,
    FuelDispatchMachine.exitOfResult, evaluateFuelJoin, evaluateApply, applyFinish_clean, applied,
    MoveApplyMachine.success, evaluateApplyJoin, addSteps]
  congr 1
  omega

/-- Parser failure restores the current certificate suffix, after the decrement. -/
theorem runEvaluation_parse_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun certificate).1 = none) :
    runEvaluation fuel certificate source target =
      ⟨false, cleanData nextFuel certificate source target,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          MoveParserMachine.fullSteps certificate + 4⟩ := by
  have actual := runEvaluation_move_failure fuel nextFuel certificate source target
    MoveApplyMachine.parseFailure (moveCleanData certificate source)
    (MoveParserMachine.fullSteps certificate + 1) nonempty decremented
    (move_clean_parse_failure certificate source failed) (by intro h; cases h)
  simpa only [moveCleanData, MoveApplyMachine.entryData, liftMoveData, cleanData, Nat.add_assoc] using actual

/-- A parsed failed rotation retains the actual unvisited path suffix and the
literal restored source, while preserving the actual certificate rest. -/
theorem runEvaluation_rotation_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word) (path : List Branch)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.rotationFailure, { certificate := rest, source := source, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runEvaluation fuel certificate source target =
      ⟨false, { (cleanData nextFuel rest source target) with path := path },
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          (2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position) + 3⟩ := by
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  exact runEvaluation_move_failure fuel nextFuel certificate source target
    MoveApplyMachine.rotationFailure _ _ nonempty decremented applied (by intro h; cases h)

/-- A successful clean raw call returns with all auxiliaries empty and the same
source length; this recurrence uses its actual returned raw output. -/
theorem runEvaluation_step (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest output : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runEvaluation fuel certificate source target =
      addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          (2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position) + 3)
        (runEvaluation nextFuel rest output target) := by
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  exact runEvaluation_move_success fuel nextFuel certificate source target _ _
    nonempty decremented applied

@[simp] theorem runSteps_nil (fuel : Bits) (source target : Word) :
    runSteps fuel [] source target = TreeEqualityMachine.runSteps source target + 3 := by
  rw [runSteps, runEvaluation_nil]

theorem runSteps_no_fuel (fuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    runSteps fuel certificate source target =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2 := by
  rw [runSteps, runEvaluation_no_fuel fuel certificate source target nonempty failed]

/-- The exact H segment clock is already inclusive of its internal parser
success/failure dispatch; the Stream controller adds its own three activations. -/
theorem runSteps_move_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (nonempty : certificate ≠ [])
    (failed : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source)).result ≠ MoveApplyMachine.success) :
    runSteps fuel certificate source target =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        MoveApplyMachine.runSteps certificate [] source [] [] [] + 3 := by
  let actual := MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
    (moveCleanData certificate source)
  have result := runEvaluation_move_failure fuel nextFuel certificate source target
    actual.result actual.data actual.steps nonempty decremented (by change actual = _; cases actual; rfl) failed
  exact congrArg Evaluation.steps result

private theorem clean_segment_budget (fuel source path : Nat) :
    2 * fuel + 3 * source + 3 * path + 14 ≤
      (2 * fuel + 3 * source + 7) * (path + 2) := by
  have scaled := Nat.mul_le_mul_left (2 * fuel + 3 * source + 4)
    (show 2 ≤ path + 2 by omega)
  have split : (2 * fuel + 3 * source + 7) * (path + 2) =
      (2 * fuel + 3 * source + 4) * (path + 2) + 3 * (path + 2) := by
    rw [show 2 * fuel + 3 * source + 7 = (2 * fuel + 3 * source + 4) + 3 by omega,
      Nat.add_mul]
  rw [split]
  omega

private theorem clean_parse_failure_budget (fuel source certificate : Nat)
    (positive : 0 < certificate) :
    2 * fuel + 2 * certificate + 7 ≤
      (2 * fuel + 3 * source + 7) * certificate + source + 4 := by
  have scaled := Nat.mul_le_mul_left (2 * fuel + 3 * source + 5)
    (show 1 ≤ certificate by omega)
  simp only [Nat.mul_one] at scaled
  have split : (2 * fuel + 3 * source + 7) * certificate =
      (2 * fuel + 3 * source + 5) * certificate + 2 * certificate := by
    rw [show 2 * fuel + 3 * source + 7 = (2 * fuel + 3 * source + 5) + 2 by omega,
      Nat.add_mul]
  rw [split]
  omega

private theorem clean_runSteps_bound_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits, ∀ source target : Word,
      runSteps fuel certificate source target ≤
        (2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4 := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target
      by_cases empty : certificate = []
      · subst certificate
        rw [runSteps_nil]
        have bound := TreeEqualityMachine.runSteps_le source target
        simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
        have minimum := Nat.min_le_left source.length target.length
        omega
      · have positive : 0 < certificate.length := List.length_pos_of_ne_nil empty
        have fuelBound := Resources.BinaryCounter.FixedWidthMachine.runSteps_le fuel
        cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
        | none =>
            rw [runSteps_no_fuel fuel certificate source target empty predecessor]
            have scaled := Nat.mul_le_mul_left (2 * fuel.length + 3 * source.length + 7)
              (show 1 ≤ certificate.length by omega)
            simp only [Nat.mul_one] at scaled
            omega
        | some nextFuel =>
            cases parsed : (parseMoveRun certificate).1 with
            | none =>
                have actual := congrArg Evaluation.steps
                  (runEvaluation_parse_failure fuel nextFuel certificate source target empty predecessor parsed)
                change runSteps fuel certificate source target =
                  Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
                    MoveParserMachine.fullSteps certificate + 4 at actual
                have parserBound := MoveParserMachine.fullSteps_le certificate
                have budget := clean_parse_failure_budget fuel.length source.length certificate.length positive
                omega
            | some pair =>
                rcases pair with ⟨move, rest⟩
                obtain ⟨result, output, path, applied, length, suffix, failed, succeeded⟩ :=
                  move_clean_parsed_raw certificate source move rest parsed
                have consumed := parseMoveRun_consumed_length certificate move rest parsed
                have fewer := parseMoveRun_rest_length_lt certificate move rest parsed
                have moveBound := move_clean_steps_of_some certificate source move rest parsed
                rw [applied] at moveBound
                dsimp only at moveBound
                have segmentBound := clean_segment_budget fuel.length source.length move.position.length
                cases result with
                | failure =>
                    have actual := congrArg Evaluation.steps
                      (runEvaluation_move_failure fuel nextFuel certificate source target
                        (.inr .failure) _ _ empty predecessor applied (by intro h; cases h))
                    change runSteps fuel certificate source target =
                      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
                        (2 * move.position.length + 4 +
                          PositionedRotationMachine.runSteps move.direction source move.position) + 3 at actual
                    have scaled := Nat.mul_le_mul_left (2 * fuel.length + 3 * source.length + 7)
                      (show move.position.length + 2 ≤ certificate.length by omega)
                    omega
                | success =>
                    have pathEmpty := succeeded rfl
                    subst path
                    have actual := congrArg Evaluation.steps
                      (runEvaluation_step fuel nextFuel certificate source target move rest output
                        predecessor parsed applied)
                    change runSteps fuel certificate source target =
                      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
                        (2 * move.position.length + 4 +
                          PositionedRotationMachine.runSteps move.direction source move.position) + 3) +
                        runSteps nextFuel rest output target at actual
                    have later := ih rest.length (by omega) rest rfl nextFuel output target
                    have width := Resources.BinaryCounter.decFixedRun_some_length predecessor
                    rw [width, length] at later
                    have split : (2 * fuel.length + 3 * source.length + 7) * certificate.length =
                        (2 * fuel.length + 3 * source.length + 7) * (move.position.length + 2) +
                          (2 * fuel.length + 3 * source.length + 7) * rest.length := by
                      rw [consumed, Nat.mul_add]
                    rw [split]
                    omega

/-- Uniform clean raw machine bound. This counts actual TM2 activations, with
all paid joins; it makes no claim about the different source-event tariff. -/
theorem runSteps_le (fuel : Bits) (certificate source target : Word) :
    runSteps fuel certificate source target ≤
      (2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4 :=
  clean_runSteps_bound_aux certificate.length certificate rfl fuel source target

/-- Tree representation changes only the bound's length expression. -/
theorem runSteps_code_le (fuel : Bits) (certificate : Word) (s t : BinaryTree Unit) :
    runSteps fuel certificate (treeCode s) (treeCode t) ≤
      (2 * fuel.length + 6 * s.numNodes + 10) * certificate.length + 2 * s.numNodes + 5 := by
  have bound := runSteps_le fuel certificate (treeCode s) (treeCode t)
  rw [treeCode_length] at bound
  have coefficient : 2 * fuel.length + 3 * (2 * s.numNodes + 1) + 7 =
      2 * fuel.length + 6 * s.numNodes + 10 := by omega
  rw [coefficient] at bound
  omega

private theorem clean_accept_cleanup_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits, ∀ source target : Word,
      (runEvaluation fuel certificate source target).result = true →
        ∃ finalFuel, (runEvaluation fuel certificate source target).data =
          cleanData finalFuel [] [] [] ∧ finalFuel.length = fuel.length := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target accepted
      by_cases empty : certificate = []
      · subst certificate
        rw [runEvaluation_nil] at accepted ⊢
        have same : source = target := of_decide_eq_true accepted
        subst target
        have consumed : source.drop (TreeEqualityMachine.runSteps source source) = [] := by
          rw [TreeEqualityMachine.runSteps_self]
          exact List.drop_eq_nil_of_le (by omega)
        exact ⟨fuel, by rw [consumed], rfl⟩
      · cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
        | none =>
            rw [runEvaluation_no_fuel fuel certificate source target empty predecessor] at accepted
            cases accepted
        | some nextFuel =>
            cases parsed : (parseMoveRun certificate).1 with
            | none =>
                rw [runEvaluation_parse_failure fuel nextFuel certificate source target empty predecessor parsed]
                  at accepted
                cases accepted
            | some pair =>
                rcases pair with ⟨move, rest⟩
                obtain ⟨result, output, path, applied, length, suffix, failed, succeeded⟩ :=
                  move_clean_parsed_raw certificate source move rest parsed
                cases result with
                | failure =>
                    rw [runEvaluation_move_failure fuel nextFuel certificate source target
                      (.inr .failure) _ _ empty predecessor applied (by intro h; cases h)] at accepted
                    cases accepted
                | success =>
                    have pathEmpty := succeeded rfl
                    subst path
                    have actual := runEvaluation_step fuel nextFuel certificate source target
                      move rest output predecessor parsed applied
                    rw [actual] at accepted ⊢
                    change (runEvaluation nextFuel rest output target).result = true at accepted
                    have fewer := parseMoveRun_rest_length_lt certificate move rest parsed
                    obtain ⟨finalFuel, data, width⟩ :=
                      ih rest.length (by omega) rest rfl nextFuel output target accepted
                    exact ⟨finalFuel, data,
                      width.trans (Resources.BinaryCounter.decFixedRun_some_length predecessor)⟩

/-- Acceptance actually consumes the certificate and both compared words and
leaves every auxiliary word empty. The literal returned fuel and its width remain. -/
theorem run_accept_cleanup (fuel : Bits) (certificate source target : Word)
    (accepted : (runEvaluation fuel certificate source target).result = true) :
    ∃ finalFuel, (runEvaluation fuel certificate source target).data =
      cleanData finalFuel [] [] [] ∧ finalFuel.length = fuel.length :=
  clean_accept_cleanup_aux certificate.length certificate rfl fuel source target accepted

/-- A successful source parse determines the actual raw H outcome and the
complete stopped/continued Stream data; no represented-tree premise is needed. -/
theorem runEvaluation_after_parse (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest)) :
    ∃ result output path,
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData certificate source) =
        ⟨.inr result, { certificate := rest, source := output, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      (∃ consumed, move.position = consumed ++ path) ∧
      (result = .failure → output = source) ∧
      (result = .failure →
        runEvaluation fuel certificate source target =
          ⟨false, { (cleanData nextFuel rest source target) with path := path },
            Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
              (2 * move.position.length + 4 +
                PositionedRotationMachine.runSteps move.direction source move.position) + 3⟩) ∧
      (result = .success → path = [] ∧
        runEvaluation fuel certificate source target =
          addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
              (2 * move.position.length + 4 +
                PositionedRotationMachine.runSteps move.direction source move.position) + 3)
            (runEvaluation nextFuel rest output target)) := by
  obtain ⟨result, output, path, actual, length, suffix, failed, succeeded⟩ :=
    move_clean_parsed_raw certificate source move rest parsed
  refine ⟨result, output, path, actual, length, suffix, failed, ?_, ?_⟩
  · intro failure
    subst result
    have restored := failed rfl
    subst output
    exact runEvaluation_rotation_failure fuel nextFuel certificate source target move rest path
      decremented parsed actual
  · intro success
    subst result
    have empty := succeeded rfl
    refine ⟨empty, ?_⟩
    subst path
    exact runEvaluation_step fuel nextFuel certificate source target move rest output
      decremented parsed actual

theorem runSteps_step (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest output : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runSteps fuel certificate source target =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        (2 * move.position.length + 4 +
          PositionedRotationMachine.runSteps move.direction source move.position) + 3 +
        runSteps nextFuel rest output target :=
  congrArg Evaluation.steps
    (runEvaluation_step fuel nextFuel certificate source target move rest output decremented parsed applied)

omit [DecidableEq K] in
theorem runResult_step (regs : Registers R) (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest output : Word) (ctx : ∀ k, List (Γ k))
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runResult (Λ := Λ) regs fuel certificate source target ctx =
      runResult (resetAll regs) nextFuel rest output target ctx := by
  simp only [runResult, runEvaluation_step fuel nextFuel certificate source target move rest output
    decremented parsed applied, evaluationCfg_addSteps, evaluationCfg_resetAll]


/-! ### Exact represented source values, recognition and separate observations -/

private theorem clean_source_value_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits,
      ∀ source target : BinaryTree Unit,
        (runEvaluation fuel certificate (treeCode source) (treeCode target)).result =
          (checkStreamRun fuel source target certificate).1 := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target
      cases certificate with
      | nil =>
          rw [runEvaluation_nil, checkStreamRun_nil]
          dsimp only [Resources.CallCount.tick]
          simpa only [TreeEqualityMachine.wordResult_equal_iff] using
            TreeEqualityMachine.result_code_source source target
      | cons tag raw =>
          have nonempty : tag :: raw ≠ [] := by simp
          cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
          | none =>
              rw [runEvaluation_no_fuel fuel (tag :: raw) (treeCode source) (treeCode target)
                nonempty predecessor,
                checkStreamRun_no_fuel fuel source target tag raw predecessor]
          | some nextFuel =>
              cases parsed : (parseMoveRun (tag :: raw)).1 with
              | none =>
                  rw [runEvaluation_parse_failure fuel nextFuel (tag :: raw)
                    (treeCode source) (treeCode target) nonempty predecessor parsed,
                    checkStreamRun_parse_failure fuel nextFuel source target tag raw predecessor parsed]
              | some pair =>
                  rcases pair with ⟨move, rest⟩
                  have encoded := (parseMoveRun_iff (tag :: raw) move rest).mp parsed
                  have fewer := parseMoveRun_rest_length_lt (tag :: raw) move rest parsed
                  cases executed : (applyMoveRun move source).1 with
                  | none =>
                      have actual := move_clean_represented_of_none move rest source executed
                      rw [← encoded] at actual
                      rw [runEvaluation_move_failure fuel nextFuel (tag :: raw)
                        (treeCode source) (treeCode target) MoveApplyMachine.rotationFailure _ _
                        nonempty predecessor actual (by intro h; cases h),
                        checkStreamRun_move_failure fuel nextFuel source target (tag :: raw) rest move
                          predecessor parsed executed]
                  | some nextTree =>
                      have actual := move_clean_represented_of_some move rest source nextTree executed
                      rw [← encoded] at actual
                      rw [runEvaluation_move_success fuel nextFuel (tag :: raw)
                        (treeCode source) (treeCode target) _ _ nonempty predecessor actual,
                        checkStreamRun_step fuel nextFuel source nextTree target (tag :: raw) rest move
                          predecessor parsed executed]
                      change (runEvaluation nextFuel rest (treeCode nextTree) (treeCode target)).result =
                        (checkStreamRun nextFuel nextTree target rest).1
                      exact ih rest.length (by omega) rest rfl nextFuel nextTree target

/-- The actual finite-machine Boolean is the existing measured source checker's
Boolean for every represented principal input, including all early failures. -/
theorem runEvaluation_code_value (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) :
    (runEvaluation fuel certificate (treeCode source) (treeCode target)).result =
      (checkStreamRun fuel source target certificate).1 :=
  clean_source_value_aux certificate.length certificate rfl fuel source target

/-- Source-success recursion keeps its actual next tree, literal certificate
suffix, complete physical endpoint and the unchanged source node count. -/
theorem represented_success_step (fuel nextFuel : Bits) (certificate rest : Word)
    (move : RotationMove) (source nextTree target : BinaryTree Unit)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (executed : (applyMoveRun move source).1 = some nextTree) :
    runEvaluation fuel certificate (treeCode source) (treeCode target) =
      addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          MoveApplyMachine.representedSteps move [] source [] + 3)
        (runEvaluation nextFuel rest (treeCode nextTree) (treeCode target)) ∧
      certificate = moveCode move ++ rest ∧
      certificate.length = move.position.length + 2 + rest.length ∧
      nextTree.numNodes = source.numNodes := by
  have encoded := (parseMoveRun_iff certificate move rest).mp parsed
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  have actual := move_clean_represented_of_some move rest source nextTree executed
  rw [← encoded] at actual
  exact ⟨runEvaluation_move_success fuel nextFuel certificate (treeCode source) (treeCode target)
      _ _ nonempty decremented actual,
    encoded, parseMoveRun_consumed_length certificate move rest parsed,
    applyMoveRun_numNodes move source nextTree executed⟩

/-- Failed represented application consumes precisely the parsed move and
retains the actual stopped physical path; no later source check occurs. -/
theorem represented_failure_step (fuel nextFuel : Bits) (certificate rest : Word)
    (move : RotationMove) (source target : BinaryTree Unit)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    runEvaluation fuel certificate (treeCode source) (treeCode target) =
      ⟨false, { (cleanData nextFuel rest (treeCode source) (treeCode target)) with
          path := PositionedRotationMachine.remainingPath move.position source },
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          MoveApplyMachine.representedSteps move [] source [] + 3⟩ := by
  have encoded := (parseMoveRun_iff certificate move rest).mp parsed
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  have actual := move_clean_represented_of_none move rest source failed
  rw [← encoded] at actual
  exact runEvaluation_move_failure fuel nextFuel certificate (treeCode source) (treeCode target)
    MoveApplyMachine.rotationFailure _ _ nonempty decremented actual (by intro h; cases h)

/-- This observation is the unchanged measured source checker, not TM2 time. -/
def sourceObservation (fuel : Bits) (source target : BinaryTree Unit) (certificate : Word) :
    Measured Bool Nat := checkStreamRun fuel source target certificate

@[simp] theorem sourceObservation_nil (fuel : Bits) (source target : BinaryTree Unit) :
    sourceObservation fuel source target [] =
      ((eqTreeRun source target).1, (eqTreeRun source target).2 + 1) :=
  checkStreamRun_nil fuel source target

theorem sourceObservation_no_fuel (fuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + 2) :=
  checkStreamRun_no_fuel fuel source target tag raw failed

theorem sourceObservation_parse_failure (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun (tag :: raw)).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun (tag :: raw)).2 + 2) :=
  checkStreamRun_parse_failure fuel nextFuel source target tag raw decremented failed

theorem sourceObservation_move_failure (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    sourceObservation fuel source target certificate =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
        (applyMoveRun move source).2 + 2) :=
  checkStreamRun_move_failure fuel nextFuel source target certificate rest move decremented parsed failed

theorem sourceObservation_step (fuel nextFuel : Bits) (source nextTree target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (executed : (applyMoveRun move source).1 = some nextTree) :
    sourceObservation fuel source target certificate =
      ((sourceObservation nextFuel nextTree target rest).1,
        (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
          (applyMoveRun move source).2 + (sourceObservation nextFuel nextTree target rest).2 + 1) :=
  checkStreamRun_step fuel nextFuel source nextTree target certificate rest move decremented parsed executed

theorem source_success_application_cost (move : RotationMove) (source nextTree : BinaryTree Unit)
    (executed : (applyMoveRun move source).1 = some nextTree) :
    (applyMoveRun move source).2 = 3 * move.position.length + 5 :=
  applyMoveRun_cost_of_some move source nextTree executed

theorem sourceObservation_cost_le (fuel : Bits) (source target : BinaryTree Unit) (certificate : Word) :
    (sourceObservation fuel source target certificate).2 ≤
      (3 * fuel.length + 3 * source.numNodes + 12) * certificate.length + 3 * source.numNodes + 6 :=
  checkStreamRun_cost_le fuel source target certificate

/-! ### Actual first return, whole-output converse and exact typed time -/

theorem run_localRun (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (runSteps fuel certificate source target)
      (entry regs fuel certificate source target ctx) (runResult regs fuel certificate source target ctx) :=
  phase_localRun caller inspectPhase (cleanData fuel certificate source target) regs ctx

theorem run (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps fuel certificate source target]
      (some (entry regs fuel certificate source target ctx)) =
        some (runResult regs fuel certificate source target ctx) :=
  LocalRun.iterate caller (run_localRun caller regs fuel certificate source target ctx)

theorem run_firstRun (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    FirstRun caller (entry regs fuel certificate source target ctx)
      (runSteps fuel certificate source target) (runResult regs fuel certificate source target ctx) :=
  phase_firstRun caller inspectPhase (cleanData fuel certificate source target) regs ctx

theorem run_firstResult_iff (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (result : Bool) :
    FirstResult caller (entry regs fuel certificate source target ctx) result ↔
      (runEvaluation fuel certificate source target).result = result :=
  phase_firstResult_iff caller inspectPhase (cleanData fuel certificate source target) regs ctx result

/-- Any actual first output has the complete canonical data, original external
frame, exact physical clock and the paid full-register reset. -/
theorem run_complete_first_output (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (ticks : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry regs fuel certificate source target ctx) ticks finish) :
    ticks = runSteps fuel certificate source target ∧
      finish = cfg (some (resultLabel (runEvaluation fuel certificate source target).result))
        (resetAll regs) (runEvaluation fuel certificate source target).data ctx := by
  have canonical := run_firstRun caller regs fuel certificate source target ctx
  exact LocalRun.first_unique caller
    (LocalRun.of_iterate caller first.1 first.2.2)
    (LocalRun.of_iterate caller canonical.1 canonical.2.2) first.2.1 canonical.2.1

/-- Both Boolean outcomes are characterized by actual first-return evidence. -/
theorem represented_firstResult_iff (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) (result : Bool) :
    FirstResult caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx) result ↔
      (checkStreamRun fuel source target certificate).1 = result := by
  rw [run_firstResult_iff, runEvaluation_code_value]

/-- Recognition retains the literal original certificate and the actual source
move sequence, with the binary-fuel value used only in the theorem. -/
theorem represented_accepts_iff (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx) true ↔
      ∃ moves, certificate = certCode moves ∧ Trees.Rotations.applyMoves? moves source = some target ∧
        moves.length ≤ Resources.BinaryCounter.value fuel := by
  rw [represented_firstResult_iff, checkStreamRun_iff]

/-- The complete first-output converse cancels no physical information: the
source Boolean, exact machine clock and all nine returned words occur together. -/
theorem represented_complete_first_output (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (ticks : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      ticks finish) :
    ticks = runSteps fuel certificate (treeCode source) (treeCode target) ∧
      finish = cfg (some (resultLabel (checkStreamRun fuel source target certificate).1))
        (resetAll regs) (runEvaluation fuel certificate (treeCode source) (treeCode target)).data ctx := by
  have actual := run_complete_first_output caller regs fuel certificate (treeCode source) (treeCode target)
    ctx ticks finish first
  simpa only [runEvaluation_code_value] using actual

def runInTimeExact (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      (runSteps fuel certificate source target) where
  steps := runSteps fuel certificate source target
  evals_in_steps := run caller regs fuel certificate source target ctx
  steps_le_m := Nat.le_refl _

def runInPolynomialTime (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) where
  steps := runSteps fuel certificate source target
  evals_in_steps := run caller regs fuel certificate source target ctx
  steps_le_m := runSteps_le fuel certificate source target

def representedInTimeExact (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  runInTimeExact caller regs fuel certificate (treeCode source) (treeCode target) ctx

def representedInPolynomialTime (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) where
  steps := runSteps fuel certificate (treeCode source) (treeCode target)
  evals_in_steps := run caller regs fuel certificate (treeCode source) (treeCode target) ctx
  steps_le_m := runSteps_code_le fuel certificate source target

@[simp] theorem runInTimeExact_steps (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    (runInTimeExact caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate source target := rfl

@[simp] theorem runInPolynomialTime_steps (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    (runInPolynomialTime caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate source target := rfl

@[simp] theorem representedInPolynomialTime_steps (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    (representedInPolynomialTime caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate (treeCode source) (treeCode target) := rfl

/-- The accepting represented first return is a live Boolean label with empty
certificate/tree/auxiliary words and its actual remaining fixed-width fuel. -/
theorem represented_accepting_endpoint (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (accepted : (checkStreamRun fuel source target certificate).1 = true) :
    ∃ finalFuel,
      FirstRun caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
        (runSteps fuel certificate (treeCode source) (treeCode target))
        (cfg (some (resultLabel true)) (resetAll regs) (cleanData finalFuel [] [] []) ctx) ∧
      finalFuel.length = fuel.length := by
  have actual : (runEvaluation fuel certificate (treeCode source) (treeCode target)).result = true :=
    (runEvaluation_code_value fuel certificate source target).trans accepted
  obtain ⟨finalFuel, data, width⟩ :=
    run_accept_cleanup fuel certificate (treeCode source) (treeCode target) actual
  refine ⟨finalFuel, ?_, width⟩
  have run := run_firstRun caller regs fuel certificate (treeCode source) (treeCode target) ctx
  simpa only [runResult, evaluationCfg, actual, data] using run


/-! ### Clean specialization of the explicit all-state physical allowance -/

section CleanSpace
variable [Fintype K]

omit [DecidableEq K] in
@[simp] theorem mass_cleanData (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    mass (cleanData fuel certificate source target) ctx =
      certificate.length + source.length + fuel.length + target.length + contextCells ctx := by
  simp only [mass, localCells, cleanData, List.length_nil, Nat.add_zero]

omit [DecidableEq K] in
@[simp] theorem hAllowance_cleanData (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    hAllowance (MoveApplyMachine.movePhase .start) (cleanData fuel certificate source target) ctx =
      certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
  rw [hAllowance, mass_cleanData]
  dsimp only [MoveApplyMachine.phaseDebt, MoveApplyMachine.phaseCredit,
    MoveApplyMachine.movePhase, MoveParserMachine.phaseDebt, applyData, cleanData]
  omega

omit [DecidableEq K] in
private theorem clean_inspectAllowance_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits, ∀ source target : Word,
      ∀ ctx : ∀ k, List (Γ k),
        inspectAllowance (cleanData fuel certificate source target) ctx ≤
          certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target ctx
      have initial : mass (cleanData fuel certificate source target) ctx ≤
          certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
        rw [mass_cleanData]
        omega
      by_cases empty : certificate = []
      · have emptyData : (cleanData fuel certificate source target).certificate = [] := empty
        rw [inspectAllowance, ite_eq_left emptyData]
        exact initial
      · have nonemptyData : (cleanData fuel certificate source target).certificate ≠ [] := empty
        rw [inspectAllowance, ite_eq_right nonemptyData, counterFinish_clean]
        cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
        | none =>
            rw [Resources.BinaryCounter.FixedWidthMachine.predSpec_of_none predecessor]
            exact initial
        | some nextFuel =>
            rw [Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some predecessor]
            dsimp only
            have width := Resources.BinaryCounter.decFixedRun_some_length predecessor
            have component : hAllowance (MoveApplyMachine.movePhase .start)
                (cleanData nextFuel certificate source target) ctx ≤
                certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
              rw [hAllowance_cleanData, width]
            rw [applyFinish_clean]
            dsimp only
            cases returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
                (moveCleanData certificate source)).result with
            | inl token =>
                exact max_le initial component
            | inr result => cases result with
              | failure =>
                  exact max_le initial component
              | success =>
                  obtain ⟨move, rest, output, parsed, actual, length, consumed, fewer⟩ :=
                    move_clean_success certificate source returned
                  rw [actual]
                  have later := ih rest.length (by omega) rest rfl nextFuel output target ctx
                  rw [length, width] at later
                  have continued : inspectAllowance (cleanData nextFuel rest output target) ctx ≤
                      certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
                    omega
                  exact max_le initial (max_le component continued)

omit [DecidableEq K] in
/-- The clean closed space bound follows from the meaningful dirty allowance,
using actual returned fuel width, source length and shorter certificate data. -/
theorem inspectAllowance_clean_le (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    inspectAllowance (cleanData fuel certificate source target) ctx ≤
      certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx :=
  clean_inspectAllowance_aux certificate.length certificate rfl fuel source target ctx

/-- Every actual inclusive clean prefix has the fixed closed physical bound.
The underlying arbitrary-state theorem uses its independently defined allowance. -/
theorem run_prefix_cells (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate source target)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs fuel certificate source target ctx)) =
      some reached) :
    stackCells reached ≤ certificate.length + 2 * source.length + fuel.length +
      target.length + contextCells ctx := by
  have actual := prefix_stackCells_le_dirty caller
    (entry regs fuel certificate source target ctx) n
    (by simpa only [remainingSteps_entry] using bound) reached executed
  rw [entry, allowance_phase_cfg] at actual
  exact actual.trans (inspectAllowance_clean_le fuel certificate source target ctx)

/-- The represented physical bound retains target storage and every protected
physical cell, and holds at the actual first result as well as earlier prefixes. -/
theorem represented_prefix_cells (regs : Registers R) (fuel : Bits) (certificate : Word)
    (s t : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate (treeCode s) (treeCode t))
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (entry regs fuel certificate (treeCode s) (treeCode t) ctx)) = some reached) :
    stackCells reached ≤ certificate.length + 2 * (2 * s.numNodes + 1) + fuel.length +
      (2 * t.numNodes + 1) + contextCells ctx := by
  simpa only [treeCode_length] using
    run_prefix_cells caller regs fuel certificate (treeCode s) (treeCode t) ctx n bound reached executed

end CleanSpace


/-! ### Actual universal malformed-family prefixes, endpoints and clocks -/

/-- The complete clean Fuel stage ends at its owned positive join. -/
theorem inspectStageFinish_clean_positive (fuel nextFuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel) :
    inspectStageFinish (cleanData fuel certificate source target) =
      ⟨.positive, cleanData nextFuel certificate source target,
        1 + Resources.BinaryCounter.FixedWidthMachine.runSteps fuel⟩ := by
  cases certificate with
  | nil => exact False.elim (nonempty rfl)
  | cons tag raw =>
      change (let actual := counterFinish .borrow (cleanData fuel (tag :: raw) source target)
        (⟨FuelDispatchMachine.exitOfResult actual.result, actual.data, 1 + actual.steps⟩ :
          InspectStageFinish)) = _
      rw [counterFinish_clean, Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some decremented]
      rfl

/-- Inspection, the actual predecessor and the paid positive join enter the
already installed MoveApply start without moving any other physical word. -/
theorem paid_apply_entry_localRun (regs : Registers R) (fuel nextFuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel) :
    LocalRun caller (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2)
      (entry regs fuel certificate source target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        (resetAll regs) (cleanData nextFuel certificate source target) ctx) := by
  have first := inspect_stage_localRun caller (cleanData fuel certificate source target) regs ctx
  rw [inspectStageFinish_clean_positive fuel nextFuel certificate source target nonempty decremented] at first
  have last := fuel_join_localRun caller .positive (cleanData nextFuel certificate source target)
    (resetFuel regs) ctx
  have combined := LocalRun.trans caller first last
  change LocalRun caller (1 + Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 1)
    (entry regs fuel certificate source target ctx)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
      (resetAll regs) (cleanData nextFuel certificate source target) ctx) at combined
  convert combined using 1
  omega

/-- Four actual activations reach H.start for the fixed one-bit positive fuel. -/
theorem one_fuel_apply_entry_localRun (regs : Registers R) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (nonempty : certificate ≠ []) :
    LocalRun caller 4 (entry regs [true] certificate source target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        (resetAll regs) (cleanData [false] certificate source target) ctx) :=
  paid_apply_entry_localRun caller regs [true] [false] certificate source target ctx nonempty rfl

/-- The left malformed family retains an arbitrary untouched certificate suffix
and target. Its H failure is followed by the real final paid Stream join. -/
theorem left_nodes_run (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * n + 13)
      (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate n nodeTag) target) ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.left_nodes_run localCaller certificateRest n
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (3 * n + 8)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyJoinPhase MoveApplyMachine.rotationFailure))) (resetAll regs)
      (cleanData [false] certificateRest (List.replicate n nodeTag) target) ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target ctx (by simp [moveCode])
  have last := apply_join_localRun caller MoveApplyMachine.rotationFailure
    (cleanData [false] certificateRest (List.replicate n nodeTag) target) (resetAll regs) ctx
  have combined := LocalRun.trans caller (LocalRun.trans caller first middle) last
  simp only [MoveApplyMachine.rotationFailure, applyJoinTarget, resetAll_resetAll] at combined
  convert combined using 1
  omega

/-- The right malformed family has a distinct physical clock, including m=0. -/
theorem right_nodes_run (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * m + 16)
      (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.right_nodes_run localCaller certificateRest m
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (3 * m + 11)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyJoinPhase MoveApplyMachine.rotationFailure))) (resetAll regs)
      (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target ctx (by simp [moveCode])
  have last := apply_join_localRun caller MoveApplyMachine.rotationFailure
    (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) (resetAll regs) ctx
  have combined := LocalRun.trans caller (LocalRun.trans caller first middle) last
  simp only [MoveApplyMachine.rotationFailure, applyJoinTarget, resetAll_resetAll] at combined
  convert combined using 1
  omega

theorem left_nodes_drop (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 10)
      (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
        (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
          units := List.replicate n () } ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.left_nodes_drop localCaller certificateRest n
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (2 * n + 6)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
      { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
        units := List.replicate n () } ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target ctx (by simp [moveCode])
  have combined := LocalRun.trans caller first middle
  convert combined using 1
  omega

theorem right_nodes_drop (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * m + 12)
      (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
        (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
          units := List.replicate (m + 1) () } ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.right_nodes_drop localCaller certificateRest m
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (2 * m + 8)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
      { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
        units := List.replicate (m + 1) () } ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target ctx (by simp [moveCode])
  have combined := LocalRun.trans caller first middle
  convert combined using 1
  omega

include caller in
theorem left_nodes_exact_clock (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps [true] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target =
      3 * n + 13 :=
  (LocalRun.phase_endpoint caller (q := inspectPhase)
    (left_nodes_run caller certificateRest n target regs ctx)).1

include caller in
theorem right_nodes_exact_clock (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps [true] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target =
      3 * m + 16 :=
  (LocalRun.phase_endpoint caller (q := inspectPhase)
    (right_nodes_run caller certificateRest m target regs ctx)).1

include caller in
theorem left_nodes_drop_rank (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      (resetAll regs) { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
        units := List.replicate n () } ctx : Cfg Γ Λ R) = n + 3 := by
  have rank := LocalRun.remaining caller (left_nodes_drop caller certificateRest n target regs ctx)
  change runSteps [true] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target = _ at rank
  rw [left_nodes_exact_clock caller certificateRest n target regs ctx] at rank
  omega

include caller in
theorem right_nodes_drop_rank (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      (resetAll regs) { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
        units := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) = m + 4 := by
  have rank := LocalRun.remaining caller (right_nodes_drop caller certificateRest m target regs ctx)
  change runSteps [true] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target = _ at rank
  rw [right_nodes_exact_clock caller certificateRest m target regs ctx] at rank
  omega

section SharpSpace
variable [Fintype K]

/-- The clean Fuel prefix conserves the actual sum of every physical store,
including the protected source/target and all external words. -/
theorem clean_fuel_prefix_cells (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (nonempty : certificate ≠ []) (n : Nat)
    (bound : n ≤ Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 1)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs fuel certificate source target ctx)) = some reached) :
    stackCells reached = mass (cleanData fuel certificate source target) ctx := by
  let D := cleanData fuel certificate source target
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := FuelDispatchMachine.cfg (some FuelDispatchMachine.inspectLabel)
    regs fuel [] certificate (fuelContext D ctx)
  have startMap : fuelCfg start = entry regs fuel certificate source target ctx := by
    change fuelCfg (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) = _
    rw [fuelCfg_view]
    rfl
  have clock : FuelDispatchMachine.dispatchSteps fuel certificate =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 1 := by
    cases certificate with
    | nil => exact False.elim (nonempty rfl)
    | cons tag raw => rfl
  obtain ⟨middle, run, rank, path, owned, reset⟩ :=
    FuelDispatchMachine.dispatch_prefix localCaller fuel certificate regs (fuelContext D ctx) n (by omega)
  have earlier : ∀ j, j < n → ∃ reached,
      (FuelDispatchMachine.next localCaller)^[j] (some start) = some reached ∧
        FuelDispatchMachine.Owned reached.l := by
    intro j strict
    obtain ⟨reached, run, rank, path, owned, reset⟩ :=
      FuelDispatchMachine.dispatch_prefix localCaller fuel certificate regs (fuelContext D ctx) j (by omega)
    exact ⟨reached, run, owned.mp (by omega)⟩
  have transported := fuel_prefix_transport caller localCaller n start earlier
  change (FuelDispatchMachine.next localCaller)^[n] (some start) = some middle at run
  rw [startMap, run] at transported
  simp only [Option.map_some] at transported
  have same : reached = fuelCfg middle := Option.some.inj (executed.symm.trans transported)
  rw [same, stackCells_fuelCfg]
  have cells := (FuelDispatchMachine.local_reaches_preserves localCaller path).2.2.2
  change FuelDispatchMachine.stackCells middle = FuelDispatchMachine.stackCells start at cells
  rw [cells, ← stackCells_fuelCfg start, startMap]
  exact stackCells_cfg _ _ _ _

/-- The paid positive join preserves cells too; the one-bit prefix has exactly
four actual activations and constant complete physical mass. -/
theorem one_fuel_prefix_cells (regs : Registers R) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (nonempty : certificate ≠ []) (n : Nat)
    (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs [true] certificate source target ctx)) = some reached) :
    stackCells reached = mass (cleanData [true] certificate source target) ctx := by
  by_cases early : n ≤ 3
  · exact clean_fuel_prefix_cells caller regs [true] certificate source target ctx
      nonempty n early reached executed
  · have four : n = 4 := by omega
    subst n
    have actual := LocalRun.iterate caller
      (one_fuel_apply_entry_localRun caller regs certificate source target ctx nonempty)
    have same := Option.some.inj (executed.symm.trans actual)
    rw [same, stackCells_cfg, mass_cleanData, mass_cleanData]
    rfl

/-- Transport an arbitrary quantitative prefix fact of the actual installed H
program. Strict earlier ownership follows from its real remaining clock. -/
theorem apply_prefix_bound
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (ticks peak : Nat)
    (clock : ticks ≤ MoveApplyMachine.remainingSteps start)
    (cells : ∀ j, j ≤ ticks → ∀ reached,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some reached →
        MoveApplyMachine.stackCells reached ≤ peak)
    (n : Nat) (bound : n ≤ ticks) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    stackCells reached ≤ peak := by
  obtain ⟨middle, run, rank, path, owned⟩ :=
    MoveApplyMachine.owned_prefix localCaller start n (by omega)
  have earlier : ∀ j, j < n → ∃ reached,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some reached ∧
        MoveApplyMachine.Owned reached.l := by
    intro j strict
    exact MoveApplyMachine.LocalRun.owned_prefix localCaller
      (MoveApplyMachine.cfg_localRun localCaller start) j (by omega)
  have transported := apply_prefix_transport caller localCaller n start earlier
  rw [run] at transported
  simp only [Option.map_some] at transported
  have same : reached = applyCfg middle := Option.some.inj (executed.symm.trans transported)
  rw [same, stackCells_applyCfg]
  exact cells n bound middle run

omit [DecidableEq K] in
theorem left_nodes_drop_cells (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      regs { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
        units := List.replicate n () } ctx : Cfg Γ Λ R) =
      2 * n + certificateRest.length + 1 + target.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [mass, localCells, cleanData, List.length_nil, List.length_cons, List.length_replicate]
  omega

omit [DecidableEq K] in
theorem right_nodes_drop_cells (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      regs { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
        units := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) =
      2 * m + 3 + certificateRest.length + 1 + target.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [mass, localCells, cleanData, List.length_nil, List.length_cons, List.length_replicate]
  omega

/-- Every actual prefix, including the paid final join, satisfies the left
family's sharp physical maximum. No tree-validity assumption is introduced. -/
theorem left_nodes_prefix_cells (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (bound : j ≤ 3 * n + 13)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)) = some reached) :
    stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + 1 + target.length + contextCells ctx := by
  have nonempty : moveCode (⟨.left, []⟩ : RotationMove) ++ certificateRest ≠ [] := by simp [moveCode]
  by_cases early : j ≤ 4
  · have cells := one_fuel_prefix_cells caller regs
      (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target ctx nonempty j early reached executed
    rw [cells, mass_cleanData]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    have lower := Nat.le_max_left (n + 2) (2 * n)
    omega
  · by_cases middle : j ≤ 4 + (3 * n + 8)
    · let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
      let frame := cleanData [false] [] [] target
      let localStart : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm (resetAll regs))
        (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] (applyContext frame ctx)
      have startMap : applyCfg localStart =
          cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
            (cleanData [false] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target) ctx := by
        simp only [localStart, MoveApplyMachine.entry, applyCfg_partial]
        rfl
      have after : (next caller)^[j - 4] (some (applyCfg localStart)) = some reached := by
        rw [startMap, ← prefix_iterate_after_localRun caller
          (one_fuel_apply_entry_localRun caller regs (moveCode ⟨.left, []⟩ ++ certificateRest)
            (List.replicate n nodeTag) target ctx nonempty) (j - 4)]
        simpa only [show 4 + (j - 4) = j by omega] using executed
      have clock : MoveApplyMachine.remainingSteps localStart = 3 * n + 8 :=
        MoveApplyMachine.left_nodes_exact_clock localCaller certificateRest n
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
      have cells := apply_prefix_bound caller localCaller localStart (3 * n + 8)
        (max (n + 2) (2 * n) + certificateRest.length + MoveApplyMachine.contextCells (applyContext frame ctx))
        (by omega)
        (MoveApplyMachine.left_nodes_prefix_cells localCaller certificateRest n
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx))
        (j - 4) (by omega) reached after
      rw [applyContext_cells] at cells
      dsimp only [frame, cleanData] at cells
      simp only [List.length_cons, List.length_nil] at cells
      omega
    · have final : j = 3 * n + 13 := by omega
      subst j
      have actual := LocalRun.iterate caller (left_nodes_run caller certificateRest n target regs ctx)
      have same := Option.some.inj (executed.symm.trans actual)
      rw [same, stackCells_cfg, mass_cleanData]
      simp only [List.length_replicate, List.length_cons, List.length_nil]
      have lower := Nat.le_max_left (n + 2) (2 * n)
      omega

/-- The right upper bound uses H's proved universal sharp bound, including its
small-input entry maximum and all later marker-restoration prefixes. -/
theorem right_nodes_prefix_cells (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (bound : j ≤ 3 * m + 16)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)) = some reached) :
    stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + 1 + target.length + contextCells ctx := by
  have nonempty : moveCode (⟨.right, []⟩ : RotationMove) ++ certificateRest ≠ [] := by simp [moveCode]
  by_cases early : j ≤ 4
  · have cells := one_fuel_prefix_cells caller regs
      (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target ctx nonempty j early reached executed
    rw [cells, mass_cleanData]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    have lower := Nat.le_max_left (m + 4) (2 * m + 3)
    omega
  · by_cases middle : j ≤ 4 + (3 * m + 11)
    · let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
      let frame := cleanData [false] [] [] target
      let localStart : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm (resetAll regs))
        (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] (applyContext frame ctx)
      have startMap : applyCfg localStart =
          cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
            (cleanData [false] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target) ctx := by
        simp only [localStart, MoveApplyMachine.entry, applyCfg_partial]
        rfl
      have after : (next caller)^[j - 4] (some (applyCfg localStart)) = some reached := by
        rw [startMap, ← prefix_iterate_after_localRun caller
          (one_fuel_apply_entry_localRun caller regs (moveCode ⟨.right, []⟩ ++ certificateRest)
            (List.replicate (m + 2) nodeTag) target ctx nonempty) (j - 4)]
        simpa only [show 4 + (j - 4) = j by omega] using executed
      have clock : MoveApplyMachine.remainingSteps localStart = 3 * m + 11 :=
        MoveApplyMachine.right_nodes_exact_clock localCaller certificateRest m
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
      have cells := apply_prefix_bound caller localCaller localStart (3 * m + 11)
        (max (m + 4) (2 * m + 3) + certificateRest.length + MoveApplyMachine.contextCells (applyContext frame ctx))
        (by omega)
        (MoveApplyMachine.right_nodes_prefix_cells localCaller certificateRest m
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx))
        (j - 4) (by omega) reached after
      rw [applyContext_cells] at cells
      dsimp only [frame, cleanData] at cells
      simp only [List.length_cons, List.length_nil] at cells
      omega
    · have final : j = 3 * m + 16 := by omega
      subst j
      have actual := LocalRun.iterate caller (right_nodes_run caller certificateRest m target regs ctx)
      have same := Option.some.inj (executed.symm.trans actual)
      rw [same, stackCells_cfg, mass_cleanData]
      simp only [List.length_replicate, List.length_cons, List.length_nil]
      have lower := Nat.le_max_left (m + 4) (2 * m + 3)
      omega

/-- The complete exact maximum includes a universal inclusive-prefix upper
bound and an actual attaining prefix, for every n including zero. -/
theorem left_nodes_peak (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * n + 13 → ∀ reached,
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)) = some reached →
      stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + 1 + target.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * n + 13 ∧
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)) = some reached ∧
      stackCells reached = max (n + 2) (2 * n) + certificateRest.length + 1 + target.length + contextCells ctx := by
  refine ⟨left_nodes_prefix_cells caller certificateRest n target regs ctx, ?_⟩
  by_cases initial : 2 * n ≤ n + 2
  · refine ⟨0, entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
      (List.replicate n nodeTag) target ctx, by omega, rfl, ?_⟩
    rw [entry, stackCells_cfg, mass_cleanData, Nat.max_eq_left initial]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    omega
  · refine ⟨2 * n + 10,
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
          units := List.replicate n () } ctx,
      by omega, LocalRun.iterate caller (left_nodes_drop caller certificateRest n target regs ctx), ?_⟩
    rw [left_nodes_drop_cells, Nat.max_eq_right (by omega)]

/-- The right exact maximum retains its m=0 small-family split and the actual
later drop attainment; a drop-state equality alone would not prove this theorem. -/
theorem right_nodes_peak (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * m + 16 → ∀ reached,
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)) = some reached →
      stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + 1 + target.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * m + 16 ∧
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)) = some reached ∧
      stackCells reached = max (m + 4) (2 * m + 3) + certificateRest.length + 1 + target.length + contextCells ctx := by
  refine ⟨right_nodes_prefix_cells caller certificateRest m target regs ctx, ?_⟩
  by_cases initial : 2 * m + 3 ≤ m + 4
  · refine ⟨0, entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
      (List.replicate (m + 2) nodeTag) target ctx, by omega, rfl, ?_⟩
    rw [entry, stackCells_cfg, mass_cleanData, Nat.max_eq_left initial]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    omega
  · refine ⟨2 * m + 12,
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
          units := List.replicate (m + 1) () } ctx,
      by omega, LocalRun.iterate caller (right_nodes_drop caller certificateRest m target regs ctx), ?_⟩
    rw [right_nodes_drop_cells, Nat.max_eq_right (by omega)]


/-- The sharper parsed-call split retains the actual certificate suffix and
path length. This is the installed H segment through its owned result join;
it is not asserted to be the peak of the entire recursive Stream run. -/
theorem apply_clean_prefix_cells_of_some (fuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun certificate).1 = some (move, rest)) (n : Nat)
    (bound : n ≤ MoveApplyMachine.runSteps certificate [] source [] [] []) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) regs
        (cleanData fuel certificate source target) ctx)) = some reached) :
    stackCells reached ≤ max (certificate.length + source.length)
      (rest.length + move.position.length + 2 * source.length) +
        fuel.length + target.length + contextCells ctx := by
  let D := cleanData fuel certificate source target
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm regs)
    certificate [] source [] [] [] (applyContext D ctx)
  have startMap : applyCfg start =
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) regs D ctx := by
    simp only [start, MoveApplyMachine.entry, applyCfg_partial]
    rfl
  have localBound := MoveApplyMachine.prefix_stackCells_le_of_some localCaller certificate move rest []
    source [] [] [] (applyRegisterEquiv.symm regs) (applyContext D ctx) parsed
  have cells := apply_prefix_bound caller localCaller start
    (MoveApplyMachine.runSteps certificate [] source [] [] [])
    (max (MoveApplyMachine.principalCells certificate [] source [] [] [] (applyContext D ctx))
      (MoveApplyMachine.parsedCellsBound move rest [] source [] [] [] (applyContext D ctx)))
    (Nat.le_refl _) localBound n bound reached (by simpa only [startMap] using executed)
  simp only [MoveApplyMachine.principalCells, MoveApplyMachine.parsedCellsBound,
    List.length_nil, Nat.add_zero, applyContext_cells, D, cleanData] at cells
  omega

end SharpSpace


/-! ### The same clean prefix carries staged registers and physical bounds -/

@[simp] theorem representedInTimeExact_steps (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    (representedInTimeExact caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate (treeCode source) (treeCode target) := rfl

/-- The universal left-family endpoint is its actual first result. -/
theorem left_nodes_firstRun (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun caller
      (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)
      (3 * n + 13)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate n nodeTag) target) ctx) := by
  have actual := left_nodes_run caller certificateRest n target regs ctx
  exact ⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩

/-- The universal right-family endpoint is its actual first result. -/
theorem right_nodes_firstRun (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun caller
      (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)
      (3 * m + 16)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) ctx) := by
  have actual := right_nodes_run caller certificateRest m target regs ctx
  exact ⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩

section CleanSharedPrefix
variable [Fintype K]

/-- One reached configuration carries the inclusive raw execution, exact
remaining clock, local closure, ownership, zero-time identity, exact staged
registers, caller state, complete protected frame, and clean physical bound. -/
theorem run_owned_prefix (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached, (next caller)^[n]
        (some (entry regs fuel certificate source target ctx)) = some reached ∧
      remainingSteps reached = runSteps fuel certificate source target - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (entry regs fuel certificate source target ctx) reached ∧
      (n < runSteps fuel certificate source target ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate source target ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + contextCells ctx := by
  obtain ⟨reached, executed, rank, path, live, zero, staged, user, frame⟩ :=
    owned_prefix_frame caller (entry regs fuel certificate source target ctx) n
      (by simpa only [remainingSteps_entry] using bound)
  refine ⟨reached, executed, ?_, path, ?_, zero, staged, user, frame,
    run_prefix_cells caller regs fuel certificate source target ctx n bound reached executed⟩
  · simpa only [remainingSteps_entry] using rank
  · simpa only [remainingSteps_entry] using live

/-- The represented specialization retains the same actual prefix witness and
the full source/target physical lengths. -/
theorem represented_owned_prefix (regs : Registers R) (fuel : Bits) (certificate : Word)
    (s t : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate (treeCode s) (treeCode t)) :
    ∃ reached, (next caller)^[n]
        (some (entry regs fuel certificate (treeCode s) (treeCode t) ctx)) = some reached ∧
      remainingSteps reached = runSteps fuel certificate (treeCode s) (treeCode t) - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (entry regs fuel certificate (treeCode s) (treeCode t) ctx) reached ∧
      (n < runSteps fuel certificate (treeCode s) (treeCode t) ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate (treeCode s) (treeCode t) ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate (treeCode s) (treeCode t) ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ certificate.length + 2 * (2 * s.numNodes + 1) + fuel.length +
        (2 * t.numNodes + 1) + contextCells ctx := by
  simpa only [treeCode_length] using
    run_owned_prefix caller regs fuel certificate (treeCode s) (treeCode t) ctx n bound

end CleanSharedPrefix

end Resources.RotationCertificate.StreamMachine
-- END COMPLETE SOURCE SUFFIX6

