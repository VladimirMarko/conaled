import Applications.Resources.RotationCertificate.FrontEndStreamMachine.DirtyExecution

/-!
# FrontEndStreamMachine: DirtyPotential
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd
open Resources.BinaryCounter (Bits)
variable {D K Λ R : Type} {Γ : K → Type}

/-! Explicit one-step data and the fixed dirty Input credit. -/

abbrev InputControl := InputParserMachine.OwnedLabels ⊕ TreeParserMachine.Result

def inputControlLabel : InputControl → InputParserMachine.Label Λ
  | .inl phase => (InputParserMachine.ownedLabelEquiv phase).val
  | .inr result => InputParserMachine.resultLabel result

def inputTreeControl (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase) : InputControl :=
  .inl (.inl (side, phase))

def inputLocalControl (phase : InputParserMachine.Phase) : InputControl :=
  .inl (.inr (.inr (.inr phase)))

def inputTreeResultControl : InputParserMachine.TreeSide → TreeParserMachine.Result → InputControl
  | .source, .success => .inl (.inr (.inl .source))
  | .target, .success => .inl (.inr (.inl .target))
  | .source, .failure => .inr .failure
  | .target, .failure => .inl (.inr (.inr (.inl ())))

def inputTreeAdvance (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase)
    (data : InputState) : InputControl × InputState :=
  match phase with
  | .init => (inputTreeControl side .scan, { data with pending := () :: data.pending })
  | .scan => match data.raw with
    | [] => (inputTreeControl side .undo, data)
    | tag :: raw =>
        if tag = nodeTag then
          (inputTreeControl side .scan,
            { data with raw := raw, rev := nodeTag :: data.rev, pending := () :: data.pending })
        else if tag = emptyTag then
          (inputTreeControl side (if data.pending.tail = [] then .emit else .scan),
            { data with raw := raw, rev := emptyTag :: data.rev, pending := data.pending.tail })
        else (inputTreeControl side .undo, data)
  | .emit => match data.rev with
    | [] => (inputTreeResultControl side .success, data)
    | tag :: rev => (inputTreeControl side .emit,
        { data with rev := rev, outputs := Function.update data.outputs side (tag :: data.outputs side) })
  | .undo => match data.rev with
    | [] => (inputTreeControl side .dropPending, data)
    | tag :: rev => (inputTreeControl side .undo, { data with raw := tag :: data.raw, rev := rev })
  | .dropPending => match data.pending with
    | [] => (inputTreeResultControl side .failure, data)
    | _ :: pending => (inputTreeControl side .dropPending, { data with pending := pending })

def inputToReverseAdvance (side : InputParserMachine.TreeSide) (data : InputState) :
    InputControl × InputState :=
  match data.outputs side with
  | [] => (inputLocalControl (InputParserMachine.toRawPhase side), data)
  | tag :: word => (inputLocalControl (InputParserMachine.toReversePhase side),
      { data with rev := tag :: data.rev, outputs := Function.update data.outputs side word })

def inputToRawAdvance (side : InputParserMachine.TreeSide) (data : InputState) : InputControl × InputState :=
  match data.rev with
  | [] => (match side with | .source => .inr .failure | .target => inputLocalControl .restoreSep1, data)
  | tag :: rev => (inputLocalControl (InputParserMachine.toRawPhase side),
      { data with raw := tag :: data.raw, rev := rev })

def inputLocalAdvance (phase : InputParserMachine.Phase) (data : InputState) : InputControl × InputState :=
  match phase with
  | .sourceToRaw => inputToRawAdvance .source data
  | .sourceToReverse => inputToReverseAdvance .source data
  | .restoreSep1 => (inputLocalControl .sourceToReverse, { data with raw := separatorTag :: data.raw })
  | .targetToRaw => inputToRawAdvance .target data
  | .targetToReverse => inputToReverseAdvance .target data
  | .restoreSep2 => (inputLocalControl .targetToReverse, { data with raw := separatorTag :: data.raw })
  | .bitsUndo => match data.bitsReverse with
    | [] => (inputLocalControl .restoreSep2, data)
    | bit :: rest => (inputLocalControl .bitsUndo,
        { data with raw := bitTag bit :: data.raw, bitsReverse := rest })
  | .fuelUndo => match data.fuel with
    | [] => (inputLocalControl .bitsUndo, data)
    | bit :: fuel => (inputLocalControl .fuelUndo,
        { data with fuel := fuel, bitsReverse := bit :: data.bitsReverse })
  | .restoreEnd => (inputLocalControl .fuelUndo, { data with raw := endInputTag :: data.raw })
  | .eof => match data.raw with
    | [] => (.inr .success, data)
    | _ :: _ => (inputLocalControl .restoreEnd, data)
  | .bitsEmit => match data.bitsReverse with
    | [] => (inputLocalControl .eof, data)
    | bit :: rest => (inputLocalControl .bitsEmit,
        { data with fuel := bit :: data.fuel, bitsReverse := rest })
  | .bitsScan => match data.raw with
    | [] => (inputLocalControl .bitsUndo, data)
    | tag :: raw =>
        if tag = bitZeroTag then
          (inputLocalControl .bitsScan, { data with raw := raw, bitsReverse := false :: data.bitsReverse })
        else if tag = bitOneTag then
          (inputLocalControl .bitsScan, { data with raw := raw, bitsReverse := true :: data.bitsReverse })
        else if tag = endInputTag then (inputLocalControl .bitsEmit, { data with raw := raw })
        else (inputLocalControl .bitsUndo, data)

def inputSeparatorAdvance (side : InputParserMachine.TreeSide) (data : InputState) : InputControl × InputState :=
  match data.raw with
  | [] => (inputLocalControl (InputParserMachine.toReversePhase side), data)
  | tag :: raw =>
      if tag = separatorTag then
        (match side with
          | .source => inputTreeControl .target .init
          | .target => inputLocalControl .bitsScan, { data with raw := raw })
      else (inputLocalControl (InputParserMachine.toReversePhase side), data)

def inputAdvance (phase : InputParserMachine.OwnedLabels) (data : InputState) : InputControl × InputState :=
  match phase with
  | .inl (side, phase) => inputTreeAdvance side phase data
  | .inr (.inl side) => inputSeparatorAdvance side data
  | .inr (.inr (.inl _)) => inputLocalAdvance .restoreSep1 data
  | .inr (.inr (.inr phase)) => inputLocalAdvance phase data

/-- The full fixed credit, including old raw length and the target rollback debt. -/
def inputPhaseCredit (phase : InputParserMachine.OwnedLabels) (rawLength : Nat) : Nat :=
  match phase with
  | .inl (.source, .init) => rawLength + 1
  | .inl (.source, .scan) | .inl (.source, .emit) => rawLength
  | .inl (.source, .undo) | .inl (.source, .dropPending) => 0
  | .inl (.target, .init) => rawLength + 2
  | .inl (.target, .scan) => rawLength + 1
  | .inl (.target, .emit) => 2
  | .inl (.target, .undo) | .inl (.target, .dropPending) => 1
  | .inr (.inl .source) => rawLength
  | .inr (.inl .target) => 2
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr .bitsScan)) | .inr (.inr (.inr .bitsEmit)) |
      .inr (.inr (.inr .eof)) | .inr (.inr (.inr .restoreEnd)) => 3
  | .inr (.inr (.inr .fuelUndo)) | .inr (.inr (.inr .bitsUndo)) |
      .inr (.inr (.inr .restoreSep2)) => 2
  | .inr (.inr (.inr .targetToReverse)) | .inr (.inr (.inr .targetToRaw)) |
      .inr (.inr (.inr .restoreSep1)) => 1
  | .inr (.inr (.inr .sourceToReverse)) | .inr (.inr (.inr .sourceToRaw)) => 0

def inputControlCredit (control : InputControl) (data : InputState) : Nat :=
  match control with
  | .inl phase => inputPhaseCredit phase data.raw.length
  | .inr _ => 0

def inputLocalCells (data : InputState) : Nat :=
  data.raw.length + data.rev.length + data.pending.length +
    (data.outputs .source).length + (data.outputs .target).length +
    data.fuel.length + data.bitsReverse.length

def inputPotential (control : InputControl) (data : InputState) : Nat :=
  inputLocalCells data + inputControlCredit control data

@[simp] theorem inputControlLabel_tree (side : InputParserMachine.TreeSide)
    (phase : TreeParserMachine.Phase) :
    inputControlLabel (Λ := Λ) (inputTreeControl side phase) = InputParserMachine.treeLabel side phase := rfl

@[simp] theorem inputControlLabel_local (phase : InputParserMachine.Phase) :
    inputControlLabel (Λ := Λ) (inputLocalControl phase) = InputParserMachine.phaseLabel phase := rfl

@[simp] theorem inputControlLabel_result (result : TreeParserMachine.Result) :
    inputControlLabel (Λ := Λ) (.inr result) = InputParserMachine.resultLabel result := rfl

@[simp] theorem inputControlLabel_treeResult (side : InputParserMachine.TreeSide)
    (result : TreeParserMachine.Result) :
    inputControlLabel (Λ := Λ) (inputTreeResultControl side result) =
      InputParserMachine.treeResultLabel side result := by
  cases side <;> cases result <;> rfl

section InputAdvanceExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

theorem inputTreeAdvance_step (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase)
    (data : InputState) (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller (inputCfg (some (InputParserMachine.treeLabel side phase)) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputTreeAdvance side phase data).1))
        (InputParserMachine.reset regs) (inputTreeAdvance side phase data).2 ctx) := by
  simp only [inputCfg, InputParserMachine.step, InputParserMachine.cfg, InputParserMachine.treeLabel]
  cases phase with
  | init =>
      exact TreeParserMachine.init_step (InputParserMachine.handler caller) side
        data.raw data.rev data.pending regs data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
  | scan =>
      cases rawEq : data.raw with
      | nil =>
          simpa only [inputTreeAdvance, rawEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.scan_step_nil (InputParserMachine.handler caller) side data.rev data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa only [inputTreeAdvance, rawEq, ite_true, inputControlLabel_tree, InputParserMachine.treeLabel] using
              TreeParserMachine.scan_step_node (InputParserMachine.handler caller) side raw data.rev data.pending regs
                data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
          · by_cases empty : tag = emptyTag
            · subst tag
              simpa only [inputTreeAdvance, rawEq, ite_eq_right node, ite_true,
                inputControlLabel_tree, InputParserMachine.treeLabel] using
                TreeParserMachine.scan_step_empty (InputParserMachine.handler caller) side raw data.rev data.pending regs
                  data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
            · simpa only [inputTreeAdvance, rawEq, ite_eq_right node, ite_eq_right empty,
                inputControlLabel_tree, InputParserMachine.treeLabel] using
                TreeParserMachine.scan_step_foreign (InputParserMachine.handler caller) side tag raw data.rev data.pending regs
                  data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx) node empty
  | emit =>
      cases revEq : data.rev with
      | nil =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_treeResult, InputParserMachine.treeResultLabel] using
            TreeParserMachine.emit_step_nil (InputParserMachine.handler caller) side data.raw data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons tag rev =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.emit_step_cons (InputParserMachine.handler caller) side tag data.raw rev data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
  | undo =>
      cases revEq : data.rev with
      | nil =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.undo_step_nil (InputParserMachine.handler caller) side data.raw data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons tag rev =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.undo_step_cons (InputParserMachine.handler caller) side tag data.raw rev data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
  | dropPending =>
      cases pendingEq : data.pending with
      | nil =>
          simpa only [inputTreeAdvance, pendingEq, inputControlLabel_treeResult, InputParserMachine.treeResultLabel] using
            TreeParserMachine.dropPending_step_nil (InputParserMachine.handler caller) side data.raw data.rev regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons token pending =>
          cases token
          simpa only [inputTreeAdvance, pendingEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.dropPending_step_cons (InputParserMachine.handler caller) side data.raw data.rev pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)

theorem inputToReverseAdvance_step (side : InputParserMachine.TreeSide) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller
      (inputCfg (some (InputParserMachine.phaseLabel (InputParserMachine.toReversePhase side))) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputToReverseAdvance side data).1))
        (InputParserMachine.reset regs) (inputToReverseAdvance side data).2 ctx) := by
  cases selected : data.outputs side with
  | nil =>
      have restored : Function.update data.outputs side [] = data.outputs := by
        rw [← selected, Function.update_eq_self]
      have equation := InputParserMachine.toReverse_step_nil caller side data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
      rw [restored] at equation
      simpa only [inputCfg, inputToReverseAdvance, selected, inputControlLabel_local] using equation
  | cons tag word =>
      have restored : Function.update data.outputs side (tag :: word) = data.outputs := by
        rw [← selected, Function.update_eq_self]
      have equation := InputParserMachine.toReverse_step_cons caller side tag data.raw data.rev word data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
      rw [restored] at equation
      simpa only [inputCfg, inputToReverseAdvance, selected, inputControlLabel_local] using equation

theorem inputToRawAdvance_step (side : InputParserMachine.TreeSide) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller
      (inputCfg (some (InputParserMachine.phaseLabel (InputParserMachine.toRawPhase side))) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputToRawAdvance side data).1))
        (InputParserMachine.reset regs) (inputToRawAdvance side data).2 ctx) := by
  cases revEq : data.rev with
  | nil =>
      have equation := InputParserMachine.toRaw_step_nil caller side data.raw data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
      cases side <;>
        simpa only [inputCfg, inputToRawAdvance, revEq, inputControlLabel_local,
          inputControlLabel_result, InputParserMachine.afterRollback] using equation
  | cons tag rev =>
      simpa only [inputCfg, inputToRawAdvance, revEq, inputControlLabel_local] using
        InputParserMachine.toRaw_step_cons caller side tag data.raw rev data.pending
          regs data.outputs data.fuel data.bitsReverse ctx


theorem inputLocalAdvance_step (phase : InputParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller (inputCfg (some (InputParserMachine.phaseLabel phase)) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputLocalAdvance phase data).1))
        (InputParserMachine.reset regs) (inputLocalAdvance phase data).2 ctx) := by
  cases phase with
  | sourceToRaw => exact inputToRawAdvance_step caller .source data regs ctx
  | targetToRaw => exact inputToRawAdvance_step caller .target data regs ctx
  | sourceToReverse => exact inputToReverseAdvance_step caller .source data regs ctx
  | targetToReverse => exact inputToReverseAdvance_step caller .target data regs ctx
  | restoreSep1 =>
      exact InputParserMachine.restoreSep1_step caller data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
  | restoreSep2 =>
      exact InputParserMachine.restoreSep2_step caller data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
  | restoreEnd =>
      exact InputParserMachine.restoreEnd_step caller data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
  | bitsUndo =>
      cases wordEq : data.bitsReverse with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsUndo_step_nil caller data.raw data.rev data.pending
              regs data.outputs data.fuel ctx
      | cons bit rest =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsUndo_step_cons caller bit data.raw data.rev data.pending
              regs data.outputs data.fuel rest ctx
  | fuelUndo =>
      cases wordEq : data.fuel with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.fuelUndo_step_nil caller data.raw data.rev data.pending
              regs data.outputs data.bitsReverse ctx
      | cons bit fuel =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.fuelUndo_step_cons caller bit data.raw data.rev data.pending
              regs data.outputs fuel data.bitsReverse ctx
  | bitsEmit =>
      cases wordEq : data.bitsReverse with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsEmit_step_nil caller data.raw data.rev data.pending
              regs data.outputs data.fuel ctx
      | cons bit rest =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsEmit_step_cons caller bit data.raw data.rev data.pending
              regs data.outputs data.fuel rest ctx
  | eof =>
      cases rawEq : data.raw with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, rawEq, inputControlLabel] using
            InputParserMachine.eof_step_nil caller data.rev data.pending regs data.outputs
              data.fuel data.bitsReverse ctx
      | cons tag raw =>
          simpa only [inputCfg, inputLocalAdvance, rawEq, inputControlLabel_local] using
            InputParserMachine.eof_step_cons caller tag raw data.rev data.pending regs data.outputs
              data.fuel data.bitsReverse ctx
  | bitsScan =>
      cases rawEq : data.raw with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, rawEq, inputControlLabel_local] using
            InputParserMachine.bitsScan_step_nil caller data.rev data.pending regs data.outputs
              data.fuel data.bitsReverse ctx
      | cons tag raw =>
          by_cases zero : tag = bitZeroTag
          · subst tag
            simpa only [inputCfg, inputLocalAdvance, rawEq, ite_true, inputControlLabel_local, bitTag] using
              InputParserMachine.bitsScan_step_bit caller false raw data.rev data.pending regs data.outputs
                data.fuel data.bitsReverse ctx
          · by_cases one : tag = bitOneTag
            · subst tag
              simpa only [inputCfg, inputLocalAdvance, rawEq, ite_eq_right zero, ite_true,
                inputControlLabel_local, bitTag] using
                InputParserMachine.bitsScan_step_bit caller true raw data.rev data.pending regs data.outputs
                  data.fuel data.bitsReverse ctx
            · by_cases ended : tag = endInputTag
              · subst tag
                simpa only [inputCfg, inputLocalAdvance, rawEq, ite_eq_right zero, ite_eq_right one,
                  ite_true, inputControlLabel_local] using
                  InputParserMachine.bitsScan_step_end caller raw data.rev data.pending regs data.outputs
                    data.fuel data.bitsReverse ctx
              · simpa only [inputCfg, inputLocalAdvance, rawEq, ite_eq_right zero, ite_eq_right one,
                  ite_eq_right ended, inputControlLabel_local] using
                  InputParserMachine.bitsScan_step_foreign caller tag raw data.rev data.pending regs
                    data.outputs data.fuel data.bitsReverse ctx ended zero one

theorem inputSeparatorAdvance_step (side : InputParserMachine.TreeSide) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller (inputCfg (some (InputParserMachine.treeResultLabel side .success)) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputSeparatorAdvance side data).1))
        (InputParserMachine.reset regs) (inputSeparatorAdvance side data).2 ctx) := by
  cases rawEq : data.raw with
  | nil =>
      simpa only [inputCfg, inputSeparatorAdvance, rawEq, inputControlLabel_local] using
        InputParserMachine.separator_step_nil caller side data.rev data.pending regs data.outputs
          data.fuel data.bitsReverse ctx
  | cons tag raw =>
      by_cases separator : tag = separatorTag
      · subst tag
        have equation := InputParserMachine.separator_step_separator caller side raw data.rev data.pending regs
          data.outputs data.fuel data.bitsReverse ctx
        cases side <;>
          simpa only [inputCfg, inputSeparatorAdvance, rawEq, ite_true, inputControlLabel_tree,
            inputControlLabel_local, InputParserMachine.afterSeparator] using equation
      · simpa only [inputCfg, inputSeparatorAdvance, rawEq, ite_eq_right separator,
          inputControlLabel_local] using
          InputParserMachine.separator_step_foreign caller side tag raw data.rev data.pending regs
            data.outputs data.fuel data.bitsReverse ctx separator

theorem inputAdvance_step (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller
      (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputAdvance phase data).1))
        (InputParserMachine.reset regs) (inputAdvance phase data).2 ctx) := by
  cases phase with
  | inl pair => exact inputTreeAdvance_step caller pair.1 pair.2 data regs ctx
  | inr phase =>
      cases phase with
      | inl side => exact inputSeparatorAdvance_step caller side data regs ctx
      | inr phase =>
          cases phase with
          | inl token =>
              exact InputParserMachine.targetFailure_step caller data.raw data.rev data.pending
                regs data.outputs data.fuel data.bitsReverse ctx
          | inr phase => exact inputLocalAdvance_step caller phase data regs ctx

end InputAdvanceExecution

def inputControlDebt : InputControl → Nat
  | .inl (.inl (side, _)) | .inl (.inr (.inl side)) => InputParserMachine.sideDebt side
  | .inl (.inr (.inr (.inl _))) => 1
  | .inl (.inr (.inr (.inr phase))) => InputParserMachine.phaseDebt phase
  | .inr .success => 3
  | .inr .failure => 0

theorem inputControlLabel_debt (control : InputControl) :
    InputParserMachine.debt (some (inputControlLabel (Λ := Λ) control)) = inputControlDebt control := by
  cases control with
  | inl phase =>
      cases phase with
      | inl pair => rfl
      | inr phase => cases phase with
        | inl side => rfl
        | inr phase => cases phase with
          | inl token => rfl
          | inr phase => rfl
  | inr result => cases result <;> rfl

def InputCreditBalance (before : InputControl) (data : InputState)
    (after : InputControl × InputState) : Prop :=
  after.2.pending.length + inputControlCredit after.1 after.2 + inputControlDebt before ≤
    data.pending.length + inputControlCredit before data + inputControlDebt after.1

theorem inputTreeAdvance_credit (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase)
    (data : InputState) :
    InputCreditBalance (inputTreeControl side phase) data (inputTreeAdvance side phase data) := by
  unfold InputCreditBalance
  cases side <;> cases phase <;> simp only [inputTreeAdvance] <;> repeat' split
  all_goals
    simp_all only [inputTreeControl, inputTreeResultControl, inputControlCredit, inputPhaseCredit,
      inputControlDebt, InputParserMachine.sideDebt, List.length_cons, List.length_nil, List.length_tail]
    omega

theorem inputLocalAdvance_credit (phase : InputParserMachine.Phase) (data : InputState) :
    InputCreditBalance (inputLocalControl phase) data (inputLocalAdvance phase data) := by
  unfold InputCreditBalance
  cases phase <;> simp only [inputLocalAdvance, inputToReverseAdvance, inputToRawAdvance] <;> repeat' split
  all_goals
    simp_all only [inputLocalControl, inputControlCredit, inputPhaseCredit,
      inputControlDebt, InputParserMachine.phaseDebt, InputParserMachine.toRawPhase,
      InputParserMachine.toReversePhase]
    omega

theorem inputSeparatorAdvance_credit (side : InputParserMachine.TreeSide) (data : InputState) :
    InputCreditBalance (inputTreeResultControl side .success) data (inputSeparatorAdvance side data) := by
  unfold InputCreditBalance
  cases side <;> simp only [inputSeparatorAdvance] <;> repeat' split
  all_goals
    simp_all only [inputTreeResultControl, inputTreeControl, inputLocalControl, inputControlCredit,
      inputPhaseCredit, inputControlDebt, InputParserMachine.sideDebt, InputParserMachine.phaseDebt,
      InputParserMachine.toReversePhase, List.length_cons]
    omega

theorem inputAdvance_credit (phase : InputParserMachine.OwnedLabels) (data : InputState) :
    InputCreditBalance (.inl phase) data (inputAdvance phase data) := by
  cases phase with
  | inl pair => exact inputTreeAdvance_credit pair.1 pair.2 data
  | inr phase =>
      cases phase with
      | inl side =>
          cases side with
          | source => exact inputSeparatorAdvance_credit .source data
          | target => exact inputSeparatorAdvance_credit .target data
      | inr phase => cases phase with
        | inl token =>
            exact inputLocalAdvance_credit .restoreSep1 data
        | inr phase => exact inputLocalAdvance_credit phase data

section InputPotentialExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

include caller in
theorem inputAdvance_potential (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    inputPotential (inputAdvance phase data).1 (inputAdvance phase data).2 ≤
      inputPotential (.inl phase) data := by
  have mass := (InputParserMachine.step_effect caller (InputParserMachine.ownedLabelEquiv phase).property
    (inputAdvance_step caller phase data regs ctx)).mass
  change InputParserMachine.baseCells
      (inputCfg (some (inputControlLabel (inputAdvance phase data).1))
        (InputParserMachine.reset regs) (inputAdvance phase data).2 ctx) +
      InputParserMachine.debt (some (inputControlLabel (inputAdvance phase data).1)) =
    InputParserMachine.baseCells
      (inputCfg (some (inputControlLabel (.inl phase))) regs data ctx) +
      InputParserMachine.debt (some (inputControlLabel (.inl phase))) at mass
  simp only [inputCfg, InputParserMachine.baseCells_cfg, InputParserMachine.outputCells,
    inputControlLabel_debt] at mass
  have credit := inputAdvance_credit phase data
  unfold InputCreditBalance at credit
  unfold inputPotential inputLocalCells
  omega

end InputPotentialExecution

/-! Actual dirty FrontEnd prefix masks and protected stores, including zero. -/

theorem frontEndInputStage_masks (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : (frontEndInputStage phase data).masks = [.input] := rfl

theorem frontEndInputOwned_tree_label (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase) :
    FrontEndMachine.inputOwnedLabel (Λ := Λ) (.inl (side, phase)) = InputParserMachine.treeLabel side phase := rfl

def frontEndComponentRegisters (mask : FrontEndMask) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R := if n = 0 then regs else mask.apply regs

def frontEndCertificateRegisters (_phase : OpenDecoderMachine.Phase)
    (_data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R := frontEndComponentRegisters .decoder regs n

def frontEndInputRegisters (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  let stage := frontEndInputStage phase data
  if n ≤ stage.steps then frontEndComponentRegisters .input regs n
  else frontEndCertificateRegisters .scan stage.data (FrontEndMask.input.apply regs) (n - stage.steps)

def frontEndInputDecoderRegisters (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  let stage := frontEndDecoderStage .input phase data
  if n ≤ stage.steps then frontEndComponentRegisters .decoder regs n
  else frontEndInputRegisters (.inl (.source, .init)) stage.data
    (FrontEndMask.decoder.apply regs) (n - stage.steps)

def frontEndFramerRegisters (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  let stage := frontEndFramerStage phase data
  if n ≤ stage.steps then frontEndComponentRegisters .framer regs n
  else frontEndInputDecoderRegisters .scan stage.data
    (FrontEndMask.framer.apply regs) (n - stage.steps)

def frontEndPhaseRegisters (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  match phase with
  | .inl phase => frontEndInputRegisters phase data regs n
  | .inr (.inl phase) => frontEndFramerRegisters phase data regs n
  | .inr (.inr (.inl phase)) => frontEndInputDecoderRegisters phase data regs n
  | .inr (.inr (.inr phase)) => frontEndCertificateRegisters phase data regs n

@[simp] theorem FrontEndMask.apply_caller (mask : FrontEndMask) (regs : FrontEndMachine.Registers R) :
    (mask.apply regs).2.2 = regs.2.2 := by cases mask <;> rfl

@[simp] theorem frontEndComponentRegisters_caller (mask : FrontEndMask)
    (regs : FrontEndMachine.Registers R) (n : Nat) :
    (frontEndComponentRegisters mask regs n).2.2 = regs.2.2 := by
  unfold frontEndComponentRegisters
  split <;> simp only [FrontEndMask.apply_caller]

theorem frontEndPhaseRegisters_caller (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    (frontEndPhaseRegisters phase data regs n).2.2 = regs.2.2 := by
  cases phase with
  | inl phase =>
      simp only [frontEndPhaseRegisters, frontEndInputRegisters, frontEndCertificateRegisters]
      split <;> simp only [frontEndComponentRegisters_caller, FrontEndMask.apply_caller]
  | inr phase =>
      cases phase with
      | inl phase =>
          simp only [frontEndPhaseRegisters, frontEndFramerRegisters, frontEndInputDecoderRegisters,
            frontEndInputRegisters, frontEndCertificateRegisters]
          repeat' split
          all_goals simp only [frontEndComponentRegisters_caller, FrontEndMask.apply_caller]
      | inr phase =>
          cases phase with
          | inl phase =>
              simp only [frontEndPhaseRegisters, frontEndInputDecoderRegisters,
                frontEndInputRegisters, frontEndCertificateRegisters]
              repeat' split
              all_goals simp only [frontEndComponentRegisters_caller, FrontEndMask.apply_caller]
          | inr phase =>
              exact frontEndComponentRegisters_caller .decoder regs n

section FrontEndPrefixExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEnd_prefix_after {start middle reached : FrontEndMachine.Cfg Γ Λ R} {first n : Nat}
    (before : (FrontEndMachine.next caller)^[first] (some start) = some middle)
    (later : first ≤ n)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    (FrontEndMachine.next caller)^[n - first] (some middle) = some reached := by
  have count : n = (n - first) + first := by omega
  rwa [count, Function.iterate_add_apply, before] at executed

theorem frontEndFramerStage_prefix_state (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndFramerStage phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .framer regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      exact ⟨rfl, fun _ => rfl⟩
  | succ n =>
      let localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
        FrontEndMachine.FramerStatement Γ Λ R := fun _ => .halt
      let localRegs := FrontEndMachine.framerRegisterEquiv.symm regs
      rw [frontEndFramerStage_steps] at bound
      obtain ⟨localReached, localEq, _, _, _, reset⟩ := OpenFramingMachine.phase_prefix localCaller phase
        data.framedRaw data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
        localRegs (FrontEndMachine.framerContext data ctx) (n + 1) bound
      have preserved := OpenFramingMachine.prefix_preserves localCaller phase data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits localRegs
        (FrontEndMachine.framerContext data ctx) (n + 1) localReached bound localEq
      have within : ∀ j, j < n + 1 → ∃ actual,
          (OpenFramingMachine.next localCaller)^[j]
            (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx)) =
              some actual ∧ OpenFramingMachine.Owned actual.l := by
        intro j strict
        obtain ⟨actual, eq, _, _, owned, _⟩ := OpenFramingMachine.phase_prefix localCaller phase
          data.framedRaw data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
          localRegs (FrontEndMachine.framerContext data ctx) j (by omega)
        exact ⟨actual, eq, owned.mp (by omega)⟩
      have translated := FrontEndMachine.framer_prefix_installed caller localCaller (n + 1)
        (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx) within
      change (OpenFramingMachine.next localCaller)^[n + 1]
        (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx)) =
          some localReached at localEq
      rw [localEq, FrontEndMachine.framerCfg_view] at translated
      simp only [Option.map_some, FrontEndMachine.framerLabelEquiv_phase, localRegs,
        Equiv.apply_symm_apply] at translated
      have same : reached = FrontEndMachine.framerCfg localReached :=
        Option.some.inj (executed.symm.trans translated)
      subst reached
      have localReset : localReached.var = OpenFramingMachine.reset localRegs :=
        Prod.ext (reset (by omega)) preserved.1
      refine ⟨?_, ?_⟩
      · change FrontEndMachine.framerRegisterEquiv localReached.var = FrontEndMachine.resetFramer regs
        rw [localReset]
        calc
          FrontEndMachine.framerRegisterEquiv (OpenFramingMachine.reset localRegs) =
              FrontEndMachine.resetFramer (FrontEndMachine.framerRegisterEquiv localRegs) :=
            FrontEndMachine.framerRegisterEquiv_reset localRegs
          _ = FrontEndMachine.resetFramer regs :=
            congrArg FrontEndMachine.resetFramer (FrontEndMachine.framerRegisterEquiv.apply_symm_apply regs)
      · intro k
        rw [FrontEndMachine.framerCfg_outside]
        exact preserved.2.1 (.inr k)

theorem frontEndInputStage_prefix_state (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndInputStage phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .input regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  let localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
    FrontEndMachine.InputStatement Γ Λ R := fun _ => .halt
  have complete := inputPhaseFinish_run localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  obtain ⟨localReached, localEq, headRun, _⟩ := complete.prefix localCaller n bound
  have translated := FrontEndMachine.input_prefix_installed caller localCaller n
    (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)
    (headRun.owned_prefix localCaller)
  change (InputParserMachine.next localCaller)^[n]
    (some (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some localReached at localEq
  rw [localEq, FrontEndMachine.inputCfg_view] at translated
  simp only [Option.map_some, frontEndInputOwned_label, FrontEndMachine.inputRegisterEquiv,
    Equiv.refl_apply] at translated
  have same : reached = FrontEndMachine.inputCfg localReached :=
    Option.some.inj (executed.symm.trans translated)
  subst reached
  refine ⟨?_, ?_⟩
  · change localReached.var = _
    exact headRun.registers localCaller
  · intro k
    rw [FrontEndMachine.inputCfg_outside]
    exact headRun.frame localCaller (.inr k)


theorem frontEndInputDecoderStage_prefix_state (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndDecoderStage .input phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .decoder regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      exact ⟨rfl, fun _ => rfl⟩
  | succ n =>
      let localCaller : OpenDecoderMachine.External (FrontEndMachine.InputDecoderCaller Λ) →
        FrontEndMachine.InputDecoderStatement Γ Λ R := fun _ => .halt
      let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
      rw [frontEndDecoderStage_steps] at bound
      obtain ⟨localReached, localEq, _, _, _, reset⟩ := OpenDecoderMachine.phase_prefix localCaller phase
        (frontEndDecoderRaw .input data) data.decodeReverse (frontEndDecoderOutput .input data)
        localRegs (FrontEndMachine.decoderContext .input data ctx) (n + 1) bound
      have preserved := OpenDecoderMachine.prefix_frame localCaller
        (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)
        localReached (n + 1) bound localEq
      have within : ∀ j, j < n + 1 → ∃ actual,
          (OpenDecoderMachine.next localCaller)^[j]
            (some (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
              some actual ∧ OpenDecoderMachine.Owned actual.l := by
        intro j strict
        obtain ⟨actual, eq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller phase
          (frontEndDecoderRaw .input data) data.decodeReverse (frontEndDecoderOutput .input data)
          localRegs (FrontEndMachine.decoderContext .input data ctx) j (by omega)
        exact ⟨actual, eq, owned.mp (by omega)⟩
      have translated := FrontEndMachine.inputDecoder_prefix_installed caller localCaller (n + 1)
        (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx) within
      change (OpenDecoderMachine.next localCaller)^[n + 1]
        (some (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some localReached at localEq
      rw [localEq, FrontEndMachine.inputDecoderCfg_view] at translated
      simp only [Option.map_some, FrontEndMachine.inputDecoderLabelEquiv_phase, localRegs,
        Equiv.apply_symm_apply] at translated
      have same : reached = FrontEndMachine.inputDecoderCfg localReached :=
        Option.some.inj (executed.symm.trans translated)
      subst reached
      have localReset : localReached.var = OpenDecoderMachine.reset localRegs :=
        Prod.ext (reset (by omega)) preserved.1
      refine ⟨?_, ?_⟩
      · change FrontEndMachine.decoderRegisterEquiv localReached.var = FrontEndMachine.afterInputDecoder regs
        rw [localReset]
        exact frontEndDecoderRegister_reset regs
      · intro k
        rw [FrontEndMachine.inputDecoderCfg_outside]
        exact preserved.2 (.inr k)

theorem frontEndCertificateDecoderStage_prefix_state (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndDecoderStage .certificate phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .decoder regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      exact ⟨rfl, fun _ => rfl⟩
  | succ n =>
      let localCaller : OpenDecoderMachine.External (FrontEndMachine.CertificateDecoderCaller Λ) →
        FrontEndMachine.CertificateDecoderStatement Γ Λ R := fun _ => .halt
      let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
      rw [frontEndDecoderStage_steps] at bound
      obtain ⟨localReached, localEq, _, _, _, reset⟩ := OpenDecoderMachine.phase_prefix localCaller phase
        (frontEndDecoderRaw .certificate data) data.decodeReverse (frontEndDecoderOutput .certificate data)
        localRegs (FrontEndMachine.decoderContext .certificate data ctx) (n + 1) bound
      have preserved := OpenDecoderMachine.prefix_frame localCaller
        (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)
        localReached (n + 1) bound localEq
      have within : ∀ j, j < n + 1 → ∃ actual,
          (OpenDecoderMachine.next localCaller)^[j]
            (some (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
              some actual ∧ OpenDecoderMachine.Owned actual.l := by
        intro j strict
        obtain ⟨actual, eq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller phase
          (frontEndDecoderRaw .certificate data) data.decodeReverse (frontEndDecoderOutput .certificate data)
          localRegs (FrontEndMachine.decoderContext .certificate data ctx) j (by omega)
        exact ⟨actual, eq, owned.mp (by omega)⟩
      have translated := FrontEndMachine.certificateDecoder_prefix_installed caller localCaller (n + 1)
        (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx) within
      change (OpenDecoderMachine.next localCaller)^[n + 1]
        (some (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some localReached at localEq
      rw [localEq, FrontEndMachine.certificateDecoderCfg_view] at translated
      simp only [Option.map_some, FrontEndMachine.certificateDecoderLabelEquiv_phase, localRegs,
        Equiv.apply_symm_apply] at translated
      have same : reached = FrontEndMachine.certificateDecoderCfg localReached :=
        Option.some.inj (executed.symm.trans translated)
      subst reached
      have localReset : localReached.var = OpenDecoderMachine.reset localRegs :=
        Prod.ext (reset (by omega)) preserved.1
      refine ⟨?_, ?_⟩
      · change FrontEndMachine.decoderRegisterEquiv localReached.var = FrontEndMachine.afterInputDecoder regs
        rw [localReset]
        exact frontEndDecoderRegister_reset regs
      · intro k
        rw [FrontEndMachine.certificateDecoderCfg_outside]
        exact preserved.2 (.inr k)


theorem frontEndInputFinish_prefix_state (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndInputFinish phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndInputRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  by_cases early : n ≤ (frontEndInputStage phase data).steps
  · simpa only [frontEndInputRegisters, ite_eq_left early] using
      frontEndInputStage_prefix_state caller phase data regs ctx n early reached executed
  · cases returned : (frontEndInputStage phase data).result with
    | failure =>
        have count : (frontEndInputFinish phase data).steps = (frontEndInputStage phase data).steps := by
          simp only [frontEndInputFinish, returned]
        rw [count] at bound
        omega
    | success =>
        have count : (frontEndInputFinish phase data).steps = (frontEndInputStage phase data).steps +
            (frontEndCertificateFinish .scan (frontEndInputStage phase data).data).steps := by
          simp only [frontEndInputFinish, returned, frontEndJoin]
        have first : (FrontEndMachine.next caller)^[(frontEndInputStage phase data).steps]
            (some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)) =
            some (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel .scan))
              (FrontEndMask.input.apply regs) (frontEndInputStage phase data).data ctx) := by
          simpa only [frontEndStageCfg, returned, frontEndInputStage_masks, frontEndMaskRegs,
            List.foldl_cons, List.foldl_nil] using
            (frontEndInputStage_trace caller phase data regs ctx).run
        have later := frontEnd_prefix_after caller first (Nat.le_of_lt (Nat.lt_of_not_ge early)) executed
        have laterBound : n - (frontEndInputStage phase data).steps ≤ (frontEndCertificateFinish .scan (frontEndInputStage phase data).data).steps := by
          rw [count] at bound
          omega
        have state := frontEndCertificateDecoderStage_prefix_state caller .scan (frontEndInputStage phase data).data
          (FrontEndMask.input.apply regs) ctx (n - (frontEndInputStage phase data).steps) laterBound reached later
        simpa only [frontEndInputRegisters, ite_eq_right early, frontEndCertificateRegisters] using state

theorem frontEndInputDecoderFinish_prefix_state (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndInputDecoderFinish phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndInputDecoderRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  by_cases early : n ≤ (frontEndDecoderStage .input phase data).steps
  · simpa only [frontEndInputDecoderRegisters, ite_eq_left early] using
      frontEndInputDecoderStage_prefix_state caller phase data regs ctx n early reached executed
  · cases returned : (frontEndDecoderStage .input phase data).result with
    | failure =>
        have count : (frontEndInputDecoderFinish phase data).steps = (frontEndDecoderStage .input phase data).steps := by
          simp only [frontEndInputDecoderFinish, returned]
        rw [count] at bound
        omega
    | success =>
        have count : (frontEndInputDecoderFinish phase data).steps = (frontEndDecoderStage .input phase data).steps +
            (frontEndInputFinish (.inl (.source, .init)) (frontEndDecoderStage .input phase data).data).steps := by
          simp only [frontEndInputDecoderFinish, returned, frontEndJoin]
        have first : (FrontEndMachine.next caller)^[(frontEndDecoderStage .input phase data).steps]
            (some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)) =
            some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel (.inl (.source, .init))))
              (FrontEndMask.decoder.apply regs) (frontEndDecoderStage .input phase data).data ctx) := by
          simpa only [frontEndStageCfg, returned, frontEndDecoderStage_masks, frontEndMaskRegs,
            List.foldl_cons, List.foldl_nil, frontEndInputOwned_tree_label] using
            (frontEndInputDecoderStage_trace caller phase data regs ctx).run
        have later := frontEnd_prefix_after caller first (Nat.le_of_lt (Nat.lt_of_not_ge early)) executed
        have laterBound : n - (frontEndDecoderStage .input phase data).steps ≤ (frontEndInputFinish (.inl (.source, .init)) (frontEndDecoderStage .input phase data).data).steps := by
          rw [count] at bound
          omega
        have state := frontEndInputFinish_prefix_state caller (.inl (.source, .init)) (frontEndDecoderStage .input phase data).data
          (FrontEndMask.decoder.apply regs) ctx (n - (frontEndDecoderStage .input phase data).steps) laterBound reached later
        simpa only [frontEndInputDecoderRegisters, ite_eq_right early] using state

theorem frontEndFramerFinish_prefix_state (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndFramerFinish phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndFramerRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  by_cases early : n ≤ (frontEndFramerStage phase data).steps
  · simpa only [frontEndFramerRegisters, ite_eq_left early] using
      frontEndFramerStage_prefix_state caller phase data regs ctx n early reached executed
  · cases returned : (frontEndFramerStage phase data).result with
    | failure =>
        have count : (frontEndFramerFinish phase data).steps = (frontEndFramerStage phase data).steps := by
          simp only [frontEndFramerFinish, returned]
        rw [count] at bound
        omega
    | success =>
        have count : (frontEndFramerFinish phase data).steps = (frontEndFramerStage phase data).steps +
            (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data).steps := by
          simp only [frontEndFramerFinish, returned, frontEndJoin]
        have first : (FrontEndMachine.next caller)^[(frontEndFramerStage phase data).steps]
            (some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)) =
            some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel .scan))
              (FrontEndMask.framer.apply regs) (frontEndFramerStage phase data).data ctx) := by
          simpa only [frontEndStageCfg, returned, frontEndFramerStage_masks, frontEndMaskRegs,
            List.foldl_cons, List.foldl_nil] using
            (frontEndFramerStage_trace caller phase data regs ctx).run
        have later := frontEnd_prefix_after caller first (Nat.le_of_lt (Nat.lt_of_not_ge early)) executed
        have laterBound : n - (frontEndFramerStage phase data).steps ≤ (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data).steps := by
          rw [count] at bound
          omega
        have state := frontEndInputDecoderFinish_prefix_state caller .scan (frontEndFramerStage phase data).data
          (FrontEndMask.framer.apply regs) ctx (n - (frontEndFramerStage phase data).steps) laterBound reached later
        simpa only [frontEndFramerRegisters, ite_eq_right early] using state

theorem frontEnd_phase_prefix_state (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) = some reached) :
    reached.var = frontEndPhaseRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases phase with
  | inl phase => exact frontEndInputFinish_prefix_state caller phase data regs ctx n bound reached executed
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerFinish_prefix_state caller phase data regs ctx n bound reached executed
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndInputDecoderFinish_prefix_state caller phase data regs ctx n bound reached executed
          | inr phase =>
              cases phase with
              | scan => exact frontEndCertificateDecoderStage_prefix_state caller .scan data regs ctx n bound reached executed
              | emit => exact frontEndCertificateDecoderStage_prefix_state caller .emit data regs ctx n bound reached executed
              | clear => exact frontEndCertificateDecoderStage_prefix_state caller .clear data regs ctx n bound reached executed

end FrontEndPrefixExecution

/-! The fixed all-dirty FrontEnd potential on actual physical local words. -/

abbrev FrontEndControl := FrontEndMachine.OwnedLabels ⊕ TreeParserMachine.Result

def frontEndControlLabel : FrontEndControl → FrontEndMachine.Label Λ
  | .inl phase => (FrontEndMachine.ownedLabelEquiv phase).val
  | .inr result => frontEndResultLabel result

def frontEndInputControl (control : InputControl) : FrontEndControl :=
  match control with
  | .inl phase => .inl (.inl phase)
  | .inr .success => .inl (.inr (.inr (.inr .scan)))
  | .inr .failure => .inr .failure

def frontEndFramerControl (phase : OpenFramingMachine.Phase) : FrontEndControl :=
  .inl (.inr (.inl phase))

def frontEndDecoderControl (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) : FrontEndControl :=
  match call with
  | .input => .inl (.inr (.inr (.inl phase)))
  | .certificate => .inl (.inr (.inr (.inr phase)))

def frontEndDecoderSuccess : FrontEndMachine.DecoderCall → FrontEndControl
  | .input => .inl (.inl (.inl (.source, .init)))
  | .certificate => .inr .success

def frontEndPhaseCredit (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : Nat :=
  match phase with
  | .inl phase => inputPhaseCredit phase data.inputRaw.length
  | .inr (.inl .scanPrefix) => data.decodeReverse.length + data.inputRaw.length
  | .inr (.inl .copyCert) | .inr (.inl .emitCert) | .inr (.inl .emitFirst) =>
      data.decodeReverse.length + data.inputRaw.length + 1
  | .inr (.inl .clearFirst) => 0
  | .inr (.inr (.inl .scan)) | .inr (.inr (.inl .emit)) =>
      data.decodeReverse.length + data.inputRaw.length + 1
  | .inr (.inr (.inl .clear)) | .inr (.inr (.inr _)) => 0

def frontEndControlCredit (control : FrontEndControl) (data : FrontEndMachine.LocalData) : Nat :=
  match control with
  | .inl phase => frontEndPhaseCredit phase data
  | .inr _ => 0

def frontEndLocalPotential (control : FrontEndControl) (data : FrontEndMachine.LocalData) : Nat :=
  FrontEndMachine.localCells data + frontEndControlCredit control data

def frontEndFramerAdvance (phase : OpenFramingMachine.Phase) (data : FrontEndMachine.LocalData) :
    FrontEndControl × FrontEndMachine.LocalData :=
  match phase with
  | .scanPrefix => match data.framedRaw with
    | [] => (frontEndFramerControl .clearFirst, data)
    | true :: raw => (frontEndFramerControl .copyCert, { data with framedRaw := raw })
    | [false] => (frontEndFramerControl .clearFirst, { data with framedRaw := [] })
    | false :: bit :: raw => (frontEndFramerControl .scanPrefix,
        { data with framedRaw := raw, frameFirstReverse := bit :: data.frameFirstReverse })
  | .copyCert => match data.framedRaw with
    | [] => (frontEndFramerControl .emitCert, data)
    | bit :: raw => (frontEndFramerControl .copyCert,
        { data with framedRaw := raw, frameCertReverse := bit :: data.frameCertReverse })
  | .emitCert => match data.frameCertReverse with
    | [] => (frontEndFramerControl .emitFirst, data)
    | bit :: rev => (frontEndFramerControl .emitCert,
        { data with frameCertReverse := rev, certificateBits := bit :: data.certificateBits })
  | .emitFirst => match data.frameFirstReverse with
    | [] => (frontEndDecoderControl .input .scan, data)
    | bit :: rev => (frontEndFramerControl .emitFirst,
        { data with frameFirstReverse := rev, inputBits := bit :: data.inputBits })
  | .clearFirst => match data.frameFirstReverse with
    | [] => (.inr .failure, data)
    | _ :: rev => (frontEndFramerControl .clearFirst, { data with frameFirstReverse := rev })

def frontEndDecoderAdvance (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    FrontEndControl × FrontEndMachine.LocalData :=
  let raw := frontEndDecoderRaw call data
  let rev := data.decodeReverse
  let out := frontEndDecoderOutput call data
  match phase with
  | .scan => match raw with
    | [] => (frontEndDecoderControl call .emit, data)
    | [_] | [_, _] | [_, _, _] =>
        (frontEndDecoderControl call .clear, frontEndWithDecoder call data [] rev out)
    | b0 :: b1 :: b2 :: b3 :: rest =>
        (frontEndDecoderControl call .scan,
          frontEndWithDecoder call data rest ((decodeTagRun b0 b1 b2 b3).1 :: rev) out)
  | .emit => match rev with
    | [] => (frontEndDecoderSuccess call, data)
    | tag :: rev => (frontEndDecoderControl call .emit,
        frontEndWithDecoder call data raw rev (tag :: out))
  | .clear => match rev with
    | [] => (.inr .failure, data)
    | _ :: rev => (frontEndDecoderControl call .clear,
        frontEndWithDecoder call data raw rev out)

def frontEndAdvance (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData) :
    FrontEndControl × FrontEndMachine.LocalData :=
  match phase with
  | .inl phase =>
      let advanced := inputAdvance phase (frontEndInputData data)
      (frontEndInputControl advanced.1, frontEndWithInput data advanced.2)
  | .inr (.inl phase) => frontEndFramerAdvance phase data
  | .inr (.inr (.inl phase)) => frontEndDecoderAdvance .input phase data
  | .inr (.inr (.inr phase)) => frontEndDecoderAdvance .certificate phase data

def frontEndPhaseMask : FrontEndMachine.OwnedLabels → FrontEndMask
  | .inl _ => .input
  | .inr (.inl _) => .framer
  | .inr (.inr _) => .decoder

theorem frontEndFramerAdvance_potential (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) :
    frontEndLocalPotential (frontEndFramerAdvance phase data).1 (frontEndFramerAdvance phase data).2 ≤
      frontEndLocalPotential (frontEndFramerControl phase) data := by
  cases phase <;> simp only [frontEndFramerAdvance] <;> repeat' split
  all_goals
    simp_all only [frontEndLocalPotential, FrontEndMachine.localCells, frontEndControlCredit,
      frontEndFramerControl, frontEndDecoderControl, frontEndPhaseCredit, List.length_cons, List.length_nil]
    omega

theorem frontEndDecoderAdvance_potential (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    frontEndLocalPotential (frontEndDecoderAdvance call phase data).1
        (frontEndDecoderAdvance call phase data).2 ≤
      frontEndLocalPotential (frontEndDecoderControl call phase) data := by
  cases call <;> cases phase <;>
    simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput] <;> repeat' split
  all_goals
    simp_all only [frontEndLocalPotential, FrontEndMachine.localCells, frontEndControlCredit,
      frontEndDecoderControl, frontEndDecoderSuccess, frontEndPhaseCredit, inputPhaseCredit,
      frontEndWithDecoder, List.length_cons, List.length_nil]
    omega

def frontEndInputOutside (data : FrontEndMachine.LocalData) : Nat :=
  data.framedRaw.length + data.frameFirstReverse.length + data.frameCertReverse.length +
    data.inputBits.length + data.certificateBits.length + data.decodeReverse.length + data.certificateWord.length

theorem frontEndLocalCells_input (data : FrontEndMachine.LocalData) :
    FrontEndMachine.localCells data = inputLocalCells (frontEndInputData data) + frontEndInputOutside data := by
  simp only [FrontEndMachine.localCells, inputLocalCells, frontEndInputData,
    InputParserMachine.treeOutputs_source, InputParserMachine.treeOutputs_target, frontEndInputOutside]
  omega

theorem frontEndLocalCells_withInput (data : FrontEndMachine.LocalData) (input : InputState) :
    FrontEndMachine.localCells (frontEndWithInput data input) = inputLocalCells input + frontEndInputOutside data := by
  simp only [FrontEndMachine.localCells, inputLocalCells, frontEndWithInput, frontEndInputOutside]
  omega

theorem frontEndInputControl_credit (control : InputControl) (data : FrontEndMachine.LocalData)
    (input : InputState) :
    frontEndControlCredit (frontEndInputControl control) (frontEndWithInput data input) =
      inputControlCredit control input := by
  cases control with
  | inl phase => rfl
  | inr result => cases result <;> rfl

@[simp] theorem frontEndControlLabel_framer (phase : OpenFramingMachine.Phase) :
    frontEndControlLabel (Λ := Λ) (frontEndFramerControl phase) = FrontEndMachine.framerLabel phase := rfl

@[simp] theorem frontEndControlLabel_decoder (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) :
    frontEndControlLabel (Λ := Λ) (frontEndDecoderControl call phase) =
      (match call with
        | .input => FrontEndMachine.inputDecoderLabel phase
        | .certificate => FrontEndMachine.certificateDecoderLabel phase) := by
  cases call <;> cases phase <;> rfl

theorem frontEndInputControl_label (control : InputControl) :
    FrontEndMachine.inputLabelEquiv
      (inputControlLabel (Λ := FrontEndMachine.ExtraLabel Λ) control) =
      frontEndControlLabel (frontEndInputControl control) := by
  cases control with
  | inl phase => rfl
  | inr result => cases result <;> rfl

section FrontEndPotentialExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEndInputAdvance_step (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel
        (frontEndInputControl (inputAdvance phase (frontEndInputData data)).1)))
        (FrontEndMask.input.apply regs)
        (frontEndWithInput data (inputAdvance phase (frontEndInputData data)).2) ctx) := by
  let localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
    FrontEndMachine.InputStatement Γ Λ R := fun _ => .halt
  let advanced := inputAdvance phase (frontEndInputData data)
  have equation := inputAdvance_step localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  have run := InputParserMachine.Runs.one localCaller (InputParserMachine.ownedLabelEquiv phase).property equation
  change InputParserMachine.Runs localCaller 1
    (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)
    (inputCfg (some (inputControlLabel advanced.1)) (InputParserMachine.reset regs) advanced.2
      (FrontEndMachine.inputContext data ctx)) at run
  have endpoint : inputCfg (some (inputControlLabel (Λ := FrontEndMachine.ExtraLabel Λ) advanced.1))
      (InputParserMachine.reset regs) advanced.2 (FrontEndMachine.inputContext data ctx) =
      FrontEndMachine.inputView (some (inputControlLabel advanced.1))
        (InputParserMachine.reset regs) (frontEndWithInput data advanced.2) ctx := by
    simp only [inputCfg, FrontEndMachine.inputView, frontEndWithInput, frontEndInput_outputs]
    rfl
  rw [endpoint] at run
  have translated := (input_trace_transport caller localCaller run).run
  rw [FrontEndMachine.inputCfg_view, FrontEndMachine.inputCfg_view] at translated
  have resetEq : InputParserMachine.reset regs = FrontEndMask.input.apply regs := rfl
  rw [resetEq] at translated
  simpa only [Function.iterate_one, FrontEndMachine.next, Option.bind_some, Option.map_some,
    frontEndInputOwned_label, frontEndInputControl_label, FrontEndMachine.inputRegisterEquiv,
    Equiv.refl_apply, FrontEndMask.apply, advanced] using translated

theorem frontEndInputAdvance_potential (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    frontEndLocalPotential (frontEndInputControl (inputAdvance phase (frontEndInputData data)).1)
        (frontEndWithInput data (inputAdvance phase (frontEndInputData data)).2) ≤
      frontEndLocalPotential (.inl (.inl phase)) data := by
  let localCaller : InputParserMachine.External Unit →
    InputParserMachine.Statement (FrontEndMachine.inputProtectedAlphabet Γ) Unit (FrontEndMachine.InputRegisterCaller R) := fun _ => .halt
  have localBound := inputAdvance_potential localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  unfold frontEndLocalPotential
  rw [frontEndLocalCells_withInput, frontEndInputControl_credit, frontEndLocalCells_input]
  change inputLocalCells (inputAdvance phase (frontEndInputData data)).2 + frontEndInputOutside data +
      inputControlCredit (inputAdvance phase (frontEndInputData data)).1
        (inputAdvance phase (frontEndInputData data)).2 ≤
    inputLocalCells (frontEndInputData data) + frontEndInputOutside data +
      inputControlCredit (.inl phase) (frontEndInputData data)
  unfold inputPotential at localBound
  omega

theorem frontEndFramer_transition (phase : OpenFramingMachine.Phase)
    (data afterData : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (afterLabel : OpenFramingMachine.Label (FrontEndMachine.FramerCaller Λ))
    (equation : OpenFramingMachine.step (fun _ => .halt)
      (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase))
        (FrontEndMachine.framerRegisterEquiv.symm regs) data ctx) =
      some (FrontEndMachine.framerView (some afterLabel)
        (OpenFramingMachine.reset (FrontEndMachine.framerRegisterEquiv.symm regs)) afterData ctx)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabelEquiv afterLabel))
        (FrontEndMask.framer.apply regs) afterData ctx) := by
  have within : ∀ j, j < 1 → ∃ reached,
      (OpenFramingMachine.next (fun _ => .halt))^[j]
        (some (FrontEndMachine.framerView (Λ := Λ) (some (OpenFramingMachine.phaseLabel phase))
          (FrontEndMachine.framerRegisterEquiv.symm regs) data ctx)) = some reached ∧
          OpenFramingMachine.Owned reached.l := by
    intro j strict
    have zero : j = 0 := by omega
    subst j
    exact ⟨_, rfl, True.intro⟩
  have translated := FrontEndMachine.framer_prefix_installed caller (fun _ => .halt) 1
    (FrontEndMachine.framerView (Λ := Λ) (some (OpenFramingMachine.phaseLabel phase))
      (FrontEndMachine.framerRegisterEquiv.symm regs) data ctx) within
  simp only [Function.iterate_one, OpenFramingMachine.next_some, equation, Option.map_some,
    FrontEndMachine.framerCfg_view, FrontEndMachine.framerLabelEquiv_phase,
    FrontEndMachine.framerRegisterEquiv_reset, Equiv.apply_symm_apply,
    FrontEndMachine.next, Option.bind_some] at translated
  exact translated


theorem frontEndFramerAdvance_step (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndFramerAdvance phase data).1))
        (FrontEndMask.framer.apply regs) (frontEndFramerAdvance phase data).2 ctx) := by
  cases phase with
  | scanPrefix =>
      cases rawEq : data.framedRaw with
      | nil =>
          simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .scanPrefix data data regs ctx
            (OpenFramingMachine.phaseLabel .clearFirst)
          simpa only [FrontEndMachine.framerView, rawEq] using
            OpenFramingMachine.scanPrefix_step_nil (fun _ => .halt)
              data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit raw =>
          cases bit with
          | false =>
              cases raw with
              | nil =>
                  simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
                  apply frontEndFramer_transition caller .scanPrefix data { data with framedRaw := [] } regs ctx
                    (OpenFramingMachine.phaseLabel .clearFirst)
                  have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := [] }) ctx =
                      FrontEndMachine.framerContext data ctx := rfl
                  simpa only [FrontEndMachine.framerView, contextEq, rawEq] using
                    OpenFramingMachine.scanPrefix_step_false_nil (fun _ => .halt)
                      data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
                      (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
              | cons bit raw =>
                  simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
                  apply frontEndFramer_transition caller .scanPrefix data
                    { data with framedRaw := raw, frameFirstReverse := bit :: data.frameFirstReverse } regs ctx
                    (OpenFramingMachine.phaseLabel .scanPrefix)
                  have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := raw, frameFirstReverse := bit :: data.frameFirstReverse }) ctx =
                      FrontEndMachine.framerContext data ctx := rfl
                  simpa only [FrontEndMachine.framerView, contextEq, rawEq] using
                    OpenFramingMachine.scanPrefix_step_false_cons (fun _ => .halt) bit raw
                      data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
                      (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
          | true =>
              simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
              apply frontEndFramer_transition caller .scanPrefix data { data with framedRaw := raw } regs ctx
                (OpenFramingMachine.phaseLabel .copyCert)
              have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := raw }) ctx =
                  FrontEndMachine.framerContext data ctx := rfl
              simpa only [FrontEndMachine.framerView, contextEq, rawEq] using
                OpenFramingMachine.scanPrefix_step_true (fun _ => .halt) raw
                  data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
                  (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | copyCert =>
      cases wordEq : data.framedRaw with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .copyCert data data regs ctx (OpenFramingMachine.phaseLabel .emitCert)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.copyCert_step_nil (fun _ => .halt) data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit raw =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .copyCert data { data with framedRaw := raw, frameCertReverse := bit :: data.frameCertReverse } regs ctx (OpenFramingMachine.phaseLabel .copyCert)
          have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := raw, frameCertReverse := bit :: data.frameCertReverse }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.copyCert_step_cons (fun _ => .halt) bit raw data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | emitCert =>
      cases wordEq : data.frameCertReverse with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .emitCert data data regs ctx (OpenFramingMachine.phaseLabel .emitFirst)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.emitCert_step_nil (fun _ => .halt) data.framedRaw data.frameFirstReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit rev =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .emitCert data { data with frameCertReverse := rev, certificateBits := bit :: data.certificateBits } regs ctx (OpenFramingMachine.phaseLabel .emitCert)
          have contextEq : FrontEndMachine.framerContext ({ data with frameCertReverse := rev, certificateBits := bit :: data.certificateBits }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.emitCert_step_cons (fun _ => .halt) bit data.framedRaw data.frameFirstReverse rev data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | emitFirst =>
      cases wordEq : data.frameFirstReverse with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_decoder]
          apply frontEndFramer_transition caller .emitFirst data data regs ctx (OpenFramingMachine.resultLabel .success)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.emitFirst_step_nil (fun _ => .halt) data.framedRaw data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit rev =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .emitFirst data { data with frameFirstReverse := rev, inputBits := bit :: data.inputBits } regs ctx (OpenFramingMachine.phaseLabel .emitFirst)
          have contextEq : FrontEndMachine.framerContext ({ data with frameFirstReverse := rev, inputBits := bit :: data.inputBits }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.emitFirst_step_cons (fun _ => .halt) bit data.framedRaw rev data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | clearFirst =>
      cases wordEq : data.frameFirstReverse with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel, frontEndResultLabel]
          apply frontEndFramer_transition caller .clearFirst data data regs ctx (OpenFramingMachine.resultLabel .failure)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.clearFirst_step_nil (fun _ => .halt) data.framedRaw data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit rev =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .clearFirst data { data with frameFirstReverse := rev } regs ctx (OpenFramingMachine.phaseLabel .clearFirst)
          have contextEq : FrontEndMachine.framerContext ({ data with frameFirstReverse := rev }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.clearFirst_step_cons (fun _ => .halt) bit data.framedRaw rev data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)


theorem frontEndInputDecoder_transition (phase : OpenDecoderMachine.Phase)
    (data afterData : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (afterLabel : OpenDecoderMachine.Label (FrontEndMachine.InputDecoderCaller Λ))
    (equation : OpenDecoderMachine.step (fun _ => .halt)
      (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase))
        (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) =
      some (FrontEndMachine.inputDecoderView (some afterLabel)
        (OpenDecoderMachine.reset (FrontEndMachine.decoderRegisterEquiv.symm regs)) afterData ctx)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabelEquiv afterLabel))
        (FrontEndMask.decoder.apply regs) afterData ctx) := by
  have within : ∀ j, j < 1 → ∃ reached,
      (OpenDecoderMachine.next (fun _ => .halt))^[j]
        (some (FrontEndMachine.inputDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
          (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx)) = some reached ∧
          OpenDecoderMachine.Owned reached.l := by
    intro j strict
    have zero : j = 0 := by omega
    subst j
    exact ⟨_, rfl, True.intro⟩
  have translated := FrontEndMachine.inputDecoder_prefix_installed caller (fun _ => .halt) 1
    (FrontEndMachine.inputDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
      (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) within
  simp only [Function.iterate_one, OpenDecoderMachine.next_some, equation, Option.map_some,
    FrontEndMachine.inputDecoderCfg_view, FrontEndMachine.inputDecoderLabelEquiv_phase,
    frontEndDecoderRegister_reset, Equiv.apply_symm_apply,
    FrontEndMachine.next, Option.bind_some] at translated
  exact translated

theorem frontEndCertificateDecoder_transition (phase : OpenDecoderMachine.Phase)
    (data afterData : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (afterLabel : OpenDecoderMachine.Label (FrontEndMachine.CertificateDecoderCaller Λ))
    (equation : OpenDecoderMachine.step (fun _ => .halt)
      (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase))
        (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) =
      some (FrontEndMachine.certificateDecoderView (some afterLabel)
        (OpenDecoderMachine.reset (FrontEndMachine.decoderRegisterEquiv.symm regs)) afterData ctx)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabelEquiv afterLabel))
        (FrontEndMask.decoder.apply regs) afterData ctx) := by
  have within : ∀ j, j < 1 → ∃ reached,
      (OpenDecoderMachine.next (fun _ => .halt))^[j]
        (some (FrontEndMachine.certificateDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
          (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx)) = some reached ∧
          OpenDecoderMachine.Owned reached.l := by
    intro j strict
    have zero : j = 0 := by omega
    subst j
    exact ⟨_, rfl, True.intro⟩
  have translated := FrontEndMachine.certificateDecoder_prefix_installed caller (fun _ => .halt) 1
    (FrontEndMachine.certificateDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
      (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) within
  simp only [Function.iterate_one, OpenDecoderMachine.next_some, equation, Option.map_some,
    FrontEndMachine.certificateDecoderCfg_view, FrontEndMachine.certificateDecoderLabelEquiv_phase,
    frontEndDecoderRegister_reset, Equiv.apply_symm_apply,
    FrontEndMachine.next, Option.bind_some] at translated
  exact translated

theorem frontEndDecoderAdvance_step (call : FrontEndMachine.DecoderCall) (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndDecoderControl call phase))) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndDecoderAdvance call phase data).1))
        (FrontEndMask.decoder.apply regs) (frontEndDecoderAdvance call phase data).2 ctx) := by
  cases call with
  | input =>
      cases phase with
      | scan =>
          cases wordEq : data.inputBits with
          | nil =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
              apply frontEndInputDecoder_transition caller .scan data data regs ctx (OpenDecoderMachine.phaseLabel .emit)
              simpa only [FrontEndMachine.inputDecoderView, wordEq] using
                OpenDecoderMachine.scan_step_nil (fun _ => .halt) data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
          | cons b0 rest =>
              cases rest with
              | nil =>
                  simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                  apply frontEndInputDecoder_transition caller .scan data
                    (frontEndWithDecoder .input data [] data.decodeReverse data.inputRaw) regs ctx
                    (OpenDecoderMachine.phaseLabel .clear)
                  simp only [FrontEndMachine.inputDecoderView]
                  rw [frontEndDecoderContext_with]
                  simpa only [frontEndWithDecoder, wordEq] using
                    OpenDecoderMachine.scan_step_one (fun _ => .halt) b0 data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
              | cons b1 rest =>
                  cases rest with
                  | nil =>
                      simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                      apply frontEndInputDecoder_transition caller .scan data
                        (frontEndWithDecoder .input data [] data.decodeReverse data.inputRaw) regs ctx
                        (OpenDecoderMachine.phaseLabel .clear)
                      simp only [FrontEndMachine.inputDecoderView]
                      rw [frontEndDecoderContext_with]
                      simpa only [frontEndWithDecoder, wordEq] using
                        OpenDecoderMachine.scan_step_two (fun _ => .halt) b0 b1 data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
                  | cons b2 rest =>
                      cases rest with
                      | nil =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                          apply frontEndInputDecoder_transition caller .scan data
                            (frontEndWithDecoder .input data [] data.decodeReverse data.inputRaw) regs ctx
                            (OpenDecoderMachine.phaseLabel .clear)
                          simp only [FrontEndMachine.inputDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_three (fun _ => .halt) b0 b1 b2 data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
                      | cons b3 rest =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, wordEq]
                          apply frontEndInputDecoder_transition caller .scan data
                            (frontEndWithDecoder .input data rest ((decodeTagRun b0 b1 b2 b3).1 :: data.decodeReverse) data.inputRaw) regs ctx
                            (OpenDecoderMachine.phaseLabel .scan)
                          simp only [FrontEndMachine.inputDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_block (fun _ => .halt) b0 b1 b2 b3 rest data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
      | emit =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndDecoderSuccess, frontEndControlLabel, frontEndResultLabel]
              apply frontEndInputDecoder_transition caller .emit data data regs ctx (OpenDecoderMachine.resultLabel .success)
              simpa only [FrontEndMachine.inputDecoderView, revEq] using
                OpenDecoderMachine.emit_step_nil (fun _ => .halt) data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndInputDecoder_transition caller .emit data
                (frontEndWithDecoder .input data data.inputBits rev (tag :: data.inputRaw)) regs ctx
                (OpenDecoderMachine.phaseLabel .emit)
              simp only [FrontEndMachine.inputDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.emit_step_cons (fun _ => .halt) tag rev data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
      | clear =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndControlLabel, frontEndResultLabel]
              apply frontEndInputDecoder_transition caller .clear data data regs ctx (OpenDecoderMachine.resultLabel .failure)
              simpa only [FrontEndMachine.inputDecoderView, revEq] using
                OpenDecoderMachine.clear_step_nil (fun _ => .halt) data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndInputDecoder_transition caller .clear data
                (frontEndWithDecoder .input data data.inputBits rev data.inputRaw) regs ctx
                (OpenDecoderMachine.phaseLabel .clear)
              simp only [FrontEndMachine.inputDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.clear_step_cons (fun _ => .halt) tag rev data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
  | certificate =>
      cases phase with
      | scan =>
          cases wordEq : data.certificateBits with
          | nil =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
              apply frontEndCertificateDecoder_transition caller .scan data data regs ctx (OpenDecoderMachine.phaseLabel .emit)
              simpa only [FrontEndMachine.certificateDecoderView, wordEq] using
                OpenDecoderMachine.scan_step_nil (fun _ => .halt) data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
          | cons b0 rest =>
              cases rest with
              | nil =>
                  simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                  apply frontEndCertificateDecoder_transition caller .scan data
                    (frontEndWithDecoder .certificate data [] data.decodeReverse data.certificateWord) regs ctx
                    (OpenDecoderMachine.phaseLabel .clear)
                  simp only [FrontEndMachine.certificateDecoderView]
                  rw [frontEndDecoderContext_with]
                  simpa only [frontEndWithDecoder, wordEq] using
                    OpenDecoderMachine.scan_step_one (fun _ => .halt) b0 data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
              | cons b1 rest =>
                  cases rest with
                  | nil =>
                      simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                      apply frontEndCertificateDecoder_transition caller .scan data
                        (frontEndWithDecoder .certificate data [] data.decodeReverse data.certificateWord) regs ctx
                        (OpenDecoderMachine.phaseLabel .clear)
                      simp only [FrontEndMachine.certificateDecoderView]
                      rw [frontEndDecoderContext_with]
                      simpa only [frontEndWithDecoder, wordEq] using
                        OpenDecoderMachine.scan_step_two (fun _ => .halt) b0 b1 data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
                  | cons b2 rest =>
                      cases rest with
                      | nil =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                          apply frontEndCertificateDecoder_transition caller .scan data
                            (frontEndWithDecoder .certificate data [] data.decodeReverse data.certificateWord) regs ctx
                            (OpenDecoderMachine.phaseLabel .clear)
                          simp only [FrontEndMachine.certificateDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_three (fun _ => .halt) b0 b1 b2 data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
                      | cons b3 rest =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, wordEq]
                          apply frontEndCertificateDecoder_transition caller .scan data
                            (frontEndWithDecoder .certificate data rest ((decodeTagRun b0 b1 b2 b3).1 :: data.decodeReverse) data.certificateWord) regs ctx
                            (OpenDecoderMachine.phaseLabel .scan)
                          simp only [FrontEndMachine.certificateDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_block (fun _ => .halt) b0 b1 b2 b3 rest data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
      | emit =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndDecoderSuccess, frontEndControlLabel, frontEndResultLabel]
              apply frontEndCertificateDecoder_transition caller .emit data data regs ctx (OpenDecoderMachine.resultLabel .success)
              simpa only [FrontEndMachine.certificateDecoderView, revEq] using
                OpenDecoderMachine.emit_step_nil (fun _ => .halt) data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndCertificateDecoder_transition caller .emit data
                (frontEndWithDecoder .certificate data data.certificateBits rev (tag :: data.certificateWord)) regs ctx
                (OpenDecoderMachine.phaseLabel .emit)
              simp only [FrontEndMachine.certificateDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.emit_step_cons (fun _ => .halt) tag rev data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
      | clear =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndControlLabel, frontEndResultLabel]
              apply frontEndCertificateDecoder_transition caller .clear data data regs ctx (OpenDecoderMachine.resultLabel .failure)
              simpa only [FrontEndMachine.certificateDecoderView, revEq] using
                OpenDecoderMachine.clear_step_nil (fun _ => .halt) data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndCertificateDecoder_transition caller .clear data
                (frontEndWithDecoder .certificate data data.certificateBits rev data.certificateWord) regs ctx
                (OpenDecoderMachine.phaseLabel .clear)
              simp only [FrontEndMachine.certificateDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.clear_step_cons (fun _ => .halt) tag rev data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)

theorem frontEndAdvance_step (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
        (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndAdvance phase data).1))
        ((frontEndPhaseMask phase).apply regs) (frontEndAdvance phase data).2 ctx) := by
  cases phase with
  | inl phase => exact frontEndInputAdvance_step caller phase data regs ctx
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerAdvance_step caller phase data regs ctx
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndDecoderAdvance_step caller .input phase data regs ctx
          | inr phase => exact frontEndDecoderAdvance_step caller .certificate phase data regs ctx

end FrontEndPotentialExecution


end Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd
