import Applications.Resources.RotationCertificate.FrontEndStreamMachine.Space

/-!
# FrontEndStreamMachine: DirtyExecution
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd

open Resources.BinaryCounter (Bits)

structure TreeState (D : Type) where
  raw : Word
  rev : Word
  pending : List Unit
  outputs : D → Word

structure TreeEnd (D : Type) where
  result : TreeParserMachine.Result
  data : TreeState D

structure TreeFinish (D : Type) extends TreeEnd D where
  steps : Nat

variable {D K Λ R : Type} {Γ : K → Type}

def treeCfg (label : Option (TreeParserMachine.Label D Λ))
    (regs : TreeParserMachine.Registers R) (data : TreeState D)
    (ctx : ∀ k, List (Γ k)) : TreeParserMachine.Cfg D Γ Λ R :=
  TreeParserMachine.cfg label regs data.raw data.rev data.pending data.outputs ctx

def treeUndoEnd (data : TreeState D) : TreeEnd D :=
  ⟨.failure, { data with raw := data.rev.reverse ++ data.raw, rev := [], pending := [] }⟩

def treeDropEnd (data : TreeState D) : TreeEnd D :=
  ⟨.failure, { data with pending := [] }⟩

def treeEmitEnd [DecidableEq D] (destination : D) (data : TreeState D) : TreeEnd D :=
  { result := .success
    data := { data with
      rev := []
      outputs := Function.update data.outputs destination
        (data.rev.reverse ++ data.outputs destination) } }

/-- Structural recursion consumes the actual raw list, even on a dirty frontier. -/
def treeScanEnd [DecidableEq D] (destination : D) :
    Word → Word → List Unit → (D → Word) → TreeEnd D
  | [], rev, pending, outputs => treeUndoEnd ⟨[], rev, pending, outputs⟩
  | tag :: raw, rev, pending, outputs =>
      if tag = nodeTag then
        treeScanEnd destination raw (nodeTag :: rev) (() :: pending) outputs
      else if tag = emptyTag then
        if pending.tail = [] then
          treeEmitEnd destination ⟨raw, emptyTag :: rev, pending.tail, outputs⟩
        else treeScanEnd destination raw (emptyTag :: rev) pending.tail outputs
      else treeUndoEnd ⟨tag :: raw, rev, pending, outputs⟩

def treePhaseEnd [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) : TreeEnd D :=
  match phase with
  | .init => treeScanEnd destination data.raw data.rev (() :: data.pending) data.outputs
  | .scan => treeScanEnd destination data.raw data.rev data.pending data.outputs
  | .emit => treeEmitEnd destination data
  | .undo => treeUndoEnd data
  | .dropPending => treeDropEnd data

/-- The existing exact physical countdown is paired with the newly explicit endpoint. -/
def treePhaseFinish [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) : TreeFinish D :=
  { treePhaseEnd destination phase data with
    steps := TreeParserMachine.phaseSteps phase data.raw data.rev data.pending }

theorem treePhaseFinish_steps [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) :
    (treePhaseFinish destination phase data).steps =
      TreeParserMachine.phaseSteps phase data.raw data.rev data.pending := rfl

theorem tree_tail_empty_iff (pending : List Unit) :
    pending.tail = [] ↔ pending.length ≤ 1 := by
  cases pending with
  | nil => simp
  | cons token pending => cases pending <;> simp

theorem treePhaseFinish_steps_pos [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) :
    0 < (treePhaseFinish destination phase data).steps := by
  rw [treePhaseFinish_steps]
  cases phase with
  | init => simp [TreeParserMachine.phaseSteps]
  | scan => exact TreeParserMachine.scanSteps_pos _ _ _
  | emit => simp [TreeParserMachine.phaseSteps]
  | undo => simp [TreeParserMachine.phaseSteps]
  | dropPending => simp [TreeParserMachine.phaseSteps]

section TreeExecution
variable [DecidableEq D] [DecidableEq K]
variable (caller : TreeParserMachine.External D Λ → TreeParserMachine.Statement D Γ Λ R)

theorem treeScanEnd_iterate (destination : D) (raw rev : Word) (pending : List Unit)
    (regs : TreeParserMachine.Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (TreeParserMachine.next caller)^[TreeParserMachine.scanSteps raw pending.length rev.length]
      (some (TreeParserMachine.cfg (some (TreeParserMachine.phaseLabel destination .scan))
        regs raw rev pending outputs ctx)) =
      some (treeCfg
        (some (TreeParserMachine.resultLabel destination (treeScanEnd destination raw rev pending outputs).result))
        (TreeParserMachine.reset regs) (treeScanEnd destination raw rev pending outputs).data ctx) := by
  induction raw generalizing rev pending regs with
  | nil =>
      simpa only [treeScanEnd, treeUndoEnd, treeCfg, TreeParserMachine.scanSteps_nil, List.append_nil] using
        TreeParserMachine.scan_nil_iterate caller destination rev pending regs outputs ctx
  | cons tag raw ih =>
      by_cases isNode : tag = nodeTag
      · subst tag
        rw [TreeParserMachine.scanSteps_node, Nat.add_comm 1 _,
          TreeParserMachine.iterate_step caller _ _ _
            (TreeParserMachine.scan_step_node caller destination raw rev pending regs outputs ctx)]
        simpa only [treeScanEnd, ite_true, List.length_cons, TreeParserMachine.reset_reset] using
          ih (nodeTag :: rev) (() :: pending) (TreeParserMachine.reset regs)
      · by_cases isEmpty : tag = emptyTag
        · subst tag
          have notNode : emptyTag ≠ nodeTag := by decide
          by_cases finished : pending.tail = []
          · have small := (tree_tail_empty_iff pending).mp finished
            rw [TreeParserMachine.scanSteps_empty, ite_eq_left small]
            have transition := TreeParserMachine.scan_step_empty caller destination raw rev pending regs outputs ctx
            simp only [finished, ite_true] at transition
            rw [show rev.length + 3 = ((emptyTag :: rev).length + 1) + 1 by simp,
              TreeParserMachine.iterate_step caller _ _ _ transition]
            simpa only [treeScanEnd, ite_eq_right notNode, ite_true, finished, treeEmitEnd,
              treeCfg, TreeParserMachine.reset_reset] using
              TreeParserMachine.emit_iterate caller destination raw (emptyTag :: rev) []
                (TreeParserMachine.reset regs) outputs ctx
          · have large : ¬ pending.length ≤ 1 := by
              intro small
              exact finished ((tree_tail_empty_iff pending).mpr small)
            rw [TreeParserMachine.scanSteps_empty, ite_eq_right large, Nat.add_comm 1 _]
            have transition := TreeParserMachine.scan_step_empty caller destination raw rev pending regs outputs ctx
            simp only [ite_eq_right finished] at transition
            rw [TreeParserMachine.iterate_step caller _ _ _ transition]
            simpa only [treeScanEnd, ite_eq_right notNode, ite_true, ite_eq_right finished,
              List.length_tail, List.length_cons, TreeParserMachine.reset_reset] using
              ih (emptyTag :: rev) pending.tail (TreeParserMachine.reset regs)
        · rw [TreeParserMachine.scanSteps_foreign tag raw pending.length rev.length isNode isEmpty]
          simpa only [treeScanEnd, ite_eq_right isNode, ite_eq_right isEmpty, treeUndoEnd, treeCfg] using
            TreeParserMachine.scan_foreign_iterate caller destination tag raw rev pending regs outputs ctx
              isNode isEmpty

theorem treePhaseFinish_iterate (destination : D) (phase : TreeParserMachine.Phase)
    (data : TreeState D) (regs : TreeParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (TreeParserMachine.next caller)^[(treePhaseFinish destination phase data).steps]
      (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
      some (treeCfg (some (TreeParserMachine.resultLabel destination
        (treePhaseFinish destination phase data).result)) (TreeParserMachine.reset regs)
        (treePhaseFinish destination phase data).data ctx) := by
  rcases data with ⟨raw, rev, pending, outputs⟩
  cases phase with
  | init =>
      simp only [treePhaseFinish, treePhaseEnd, treeCfg, TreeParserMachine.phaseSteps]
      rw [Nat.add_comm 1 _, TreeParserMachine.iterate_step caller _ _ _
        (TreeParserMachine.init_step caller destination raw rev pending regs outputs ctx)]
      simpa only [List.length_cons, TreeParserMachine.reset_reset, treeCfg] using
        treeScanEnd_iterate caller destination raw rev (() :: pending)
          (TreeParserMachine.reset regs) outputs ctx
  | scan =>
      exact treeScanEnd_iterate caller destination raw rev pending regs outputs ctx
  | emit =>
      simpa only [treePhaseFinish, treePhaseEnd, treeEmitEnd, treeCfg, TreeParserMachine.phaseSteps] using
        TreeParserMachine.emit_iterate caller destination raw rev pending regs outputs ctx
  | undo =>
      simpa only [treePhaseFinish, treePhaseEnd, treeUndoEnd, treeCfg, TreeParserMachine.phaseSteps] using
        TreeParserMachine.undo_drop_iterate caller destination raw rev pending regs outputs ctx
  | dropPending =>
      simpa only [treePhaseFinish, treePhaseEnd, treeDropEnd, treeCfg, TreeParserMachine.phaseSteps] using
        TreeParserMachine.dropPending_iterate caller destination raw rev pending regs outputs ctx

theorem treePhaseFinish_owned_prefix (destination : D) (phase : TreeParserMachine.Phase)
    (data : TreeState D) (regs : TreeParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n < (treePhaseFinish destination phase data).steps) :
    ∃ reached, (TreeParserMachine.next caller)^[n]
      (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
        some reached ∧ TreeParserMachine.Owned reached.l := by
  obtain ⟨reached, executed, _, _, owned, _⟩ := TreeParserMachine.phase_prefix caller
    destination phase data.raw data.rev data.pending regs data.outputs ctx n (Nat.le_of_lt bound)
  exact ⟨reached, executed, owned.mp bound⟩

end TreeExecution

/-! Insert after the constructive dirty Tree helper, in the same namespace. -/

structure InputState extends TreeState InputParserMachine.TreeSide where
  fuel : Bits
  bitsReverse : Bits

structure InputFinish where
  result : TreeParserMachine.Result
  data : InputState
  steps : Nat

def inputCfg (label : Option (InputParserMachine.Label Λ))
    (regs : InputParserMachine.Registers R) (data : InputState)
    (ctx : ∀ k, List (Γ k)) : InputParserMachine.Cfg Γ Λ R :=
  InputParserMachine.cfg label regs data.raw data.rev data.pending data.outputs
    data.fuel data.bitsReverse ctx

def inputAdd (ticks : Nat) (finish : InputFinish) : InputFinish :=
  { finish with steps := ticks + finish.steps }

def inputSourceToRaw (data : InputState) : InputFinish :=
  ⟨.failure, { data with raw := data.rev.reverse ++ data.raw, rev := [] }, data.rev.length + 1⟩

def inputSourceToReverse (data : InputState) : InputFinish :=
  inputAdd ((data.outputs .source).length + 1)
    (inputSourceToRaw { data with
      rev := (data.outputs .source).reverse ++ data.rev
      outputs := Function.update data.outputs .source [] })

def inputRestoreSep1 (data : InputState) : InputFinish :=
  inputAdd 1 (inputSourceToReverse { data with raw := separatorTag :: data.raw })

def inputTargetToRaw (data : InputState) : InputFinish :=
  inputAdd (data.rev.length + 1)
    (inputRestoreSep1 { data with raw := data.rev.reverse ++ data.raw, rev := [] })

def inputTargetToReverse (data : InputState) : InputFinish :=
  inputAdd ((data.outputs .target).length + 1)
    (inputTargetToRaw { data with
      rev := (data.outputs .target).reverse ++ data.rev
      outputs := Function.update data.outputs .target [] })

def inputRestoreSep2 (data : InputState) : InputFinish :=
  inputAdd 1 (inputTargetToReverse { data with raw := separatorTag :: data.raw })

def inputBitsUndo (data : InputState) : InputFinish :=
  inputAdd (data.bitsReverse.length + 1)
    (inputRestoreSep2 { data with
      raw := bitTags data.bitsReverse.reverse ++ data.raw
      bitsReverse := [] })

def inputFuelUndo (data : InputState) : InputFinish :=
  inputAdd (data.fuel.length + 1)
    (inputBitsUndo { data with fuel := [], bitsReverse := data.fuel.reverse ++ data.bitsReverse })

def inputRestoreEnd (data : InputState) : InputFinish :=
  inputAdd 1 (inputFuelUndo { data with raw := endInputTag :: data.raw })

def inputEof (data : InputState) : InputFinish :=
  if data.raw = [] then ⟨.success, data, 1⟩ else inputAdd 1 (inputRestoreEnd data)

def inputBitsEmit (data : InputState) : InputFinish :=
  inputAdd (data.bitsReverse.length + 1)
    (inputEof { data with fuel := data.bitsReverse.reverse ++ data.fuel, bitsReverse := [] })

/-- Each recursion removes one actual bit tag; the terminal branch is paid too. -/
def inputBitsScanAux : Word → InputState → InputFinish
  | [], data => inputAdd 1 (inputBitsUndo { data with raw := [] })
  | tag :: raw, data =>
      if tag = bitZeroTag then
        inputAdd 1 (inputBitsScanAux raw { data with bitsReverse := false :: data.bitsReverse })
      else if tag = bitOneTag then
        inputAdd 1 (inputBitsScanAux raw { data with bitsReverse := true :: data.bitsReverse })
      else if tag = endInputTag then
        inputAdd 1 (inputBitsEmit { data with raw := raw })
      else inputAdd 1 (inputBitsUndo { data with raw := tag :: raw })

def inputLocalFinish (phase : InputParserMachine.Phase) (data : InputState) : InputFinish :=
  match phase with
  | .sourceToRaw => inputSourceToRaw data
  | .sourceToReverse => inputSourceToReverse data
  | .restoreSep1 => inputRestoreSep1 data
  | .targetToRaw => inputTargetToRaw data
  | .targetToReverse => inputTargetToReverse data
  | .restoreSep2 => inputRestoreSep2 data
  | .bitsUndo => inputBitsUndo data
  | .fuelUndo => inputFuelUndo data
  | .restoreEnd => inputRestoreEnd data
  | .eof => inputEof data
  | .bitsEmit => inputBitsEmit data
  | .bitsScan => inputBitsScanAux data.raw data

section InputExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

def InputFinish.Run (finish : InputFinish) (label : InputParserMachine.Label Λ)
    (data : InputState) (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  InputParserMachine.Runs caller finish.steps (inputCfg (some label) regs data ctx)
    (inputCfg (some (InputParserMachine.resultLabel finish.result))
      (InputParserMachine.reset regs) finish.data ctx)

theorem InputFinish.Run.prepend {finish : InputFinish}
    {label nextLabel : InputParserMachine.Label Λ} {data nextData : InputState}
    {regs : InputParserMachine.Registers R} {ctx : ∀ k, List (Γ k)} {ticks : Nat}
    (segment : InputParserMachine.Runs caller ticks (inputCfg (some label) regs data ctx)
      (inputCfg (some nextLabel) (InputParserMachine.reset regs) nextData ctx))
    (tailRun : finish.Run caller nextLabel nextData (InputParserMachine.reset regs) ctx) :
    (inputAdd ticks finish).Run caller label data regs ctx := by
  simpa only [InputFinish.Run, inputAdd, TreeParserMachine.reset_reset] using
    segment.trans caller tailRun

theorem inputSourceToRaw_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputSourceToRaw data).Run caller (InputParserMachine.phaseLabel .sourceToRaw) data regs ctx := by
  exact InputParserMachine.toRawPhase_run caller .source data.raw data.rev data.pending regs
    data.outputs data.fuel data.bitsReverse ctx

theorem inputSourceToReverse_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputSourceToReverse data).Run caller (InputParserMachine.phaseLabel .sourceToReverse)
      data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToRaw)
    (nextData := { data with rev := (data.outputs .source).reverse ++ data.rev, outputs := Function.update data.outputs .source [] })
  · simpa only [inputCfg, Function.update_eq_self, InputParserMachine.toReversePhase, InputParserMachine.toRawPhase] using
      InputParserMachine.toReversePhase_run caller .source (data.outputs .source) data.raw data.rev
        data.pending regs data.outputs data.fuel data.bitsReverse ctx
  · exact inputSourceToRaw_run caller _ _ _

theorem inputRestoreSep1_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreSep1 data).Run caller (InputParserMachine.phaseLabel .restoreSep1) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse)
    (nextData := { data with raw := separatorTag :: data.raw })
  · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
      (InputParserMachine.restoreSep1_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputSourceToReverse_run caller _ _ _

theorem inputTargetToRaw_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputTargetToRaw data).Run caller (InputParserMachine.phaseLabel .targetToRaw) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .restoreSep1)
    (nextData := { data with raw := data.rev.reverse ++ data.raw, rev := [] })
  · exact InputParserMachine.toRawPhase_run caller .target data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputRestoreSep1_run caller _ _ _

theorem inputTargetToReverse_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputTargetToReverse data).Run caller (InputParserMachine.phaseLabel .targetToReverse)
      data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToRaw)
    (nextData := { data with rev := (data.outputs .target).reverse ++ data.rev, outputs := Function.update data.outputs .target [] })
  · simpa only [inputCfg, Function.update_eq_self, InputParserMachine.toReversePhase, InputParserMachine.toRawPhase] using
      InputParserMachine.toReversePhase_run caller .target (data.outputs .target) data.raw data.rev
        data.pending regs data.outputs data.fuel data.bitsReverse ctx
  · exact inputTargetToRaw_run caller _ _ _

theorem inputRestoreSep2_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreSep2 data).Run caller (InputParserMachine.phaseLabel .restoreSep2) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToReverse)
    (nextData := { data with raw := separatorTag :: data.raw })
  · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
      (InputParserMachine.restoreSep2_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputTargetToReverse_run caller _ _ _

theorem inputBitsUndo_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputBitsUndo data).Run caller (InputParserMachine.phaseLabel .bitsUndo) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .restoreSep2)
    (nextData := { data with raw := bitTags data.bitsReverse.reverse ++ data.raw, bitsReverse := [] })
  · exact InputParserMachine.bitsUndo_run caller data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputRestoreSep2_run caller _ _ _

theorem inputFuelUndo_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputFuelUndo data).Run caller (InputParserMachine.phaseLabel .fuelUndo) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsUndo)
    (nextData := { data with fuel := [], bitsReverse := data.fuel.reverse ++ data.bitsReverse })
  · exact InputParserMachine.fuelUndo_run caller data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputBitsUndo_run caller _ _ _

theorem inputRestoreEnd_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreEnd data).Run caller (InputParserMachine.phaseLabel .restoreEnd) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .fuelUndo)
    (nextData := { data with raw := endInputTag :: data.raw })
  · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
      (InputParserMachine.restoreEnd_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputFuelUndo_run caller _ _ _

theorem inputEof_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputEof data).Run caller (InputParserMachine.phaseLabel .eof) data regs ctx := by
  unfold inputEof
  split
  · rename_i empty
    simpa only [InputFinish.Run, inputCfg, empty] using
      InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
        (InputParserMachine.eof_step_nil caller data.rev data.pending regs data.outputs
          data.fuel data.bitsReverse ctx)
  · rename_i nonempty
    apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .restoreEnd)
      (nextData := data)
    · cases rawEq : data.raw with
      | nil => exact False.elim (nonempty rawEq)
      | cons tag raw =>
          simpa only [inputCfg, rawEq] using
            InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
              (InputParserMachine.eof_step_cons caller tag raw data.rev data.pending regs
                data.outputs data.fuel data.bitsReverse ctx)
    · exact inputRestoreEnd_run caller _ _ _

theorem inputBitsEmit_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputBitsEmit data).Run caller (InputParserMachine.phaseLabel .bitsEmit) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .eof)
    (nextData := { data with fuel := data.bitsReverse.reverse ++ data.fuel, bitsReverse := [] })
  · exact InputParserMachine.bitsEmit_run caller data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputEof_run caller _ _ _

theorem inputBitsScanAux_run (raw : Word) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputBitsScanAux raw data).Run caller (InputParserMachine.phaseLabel .bitsScan)
      { data with raw := raw } regs ctx := by
  induction raw generalizing data regs with
  | nil =>
      apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsUndo) (nextData := { data with raw := [] })
      · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
          (InputParserMachine.bitsScan_step_nil caller data.rev data.pending regs data.outputs
            data.fuel data.bitsReverse ctx)
      · exact inputBitsUndo_run caller _ _ _
  | cons tag raw ih =>
      unfold inputBitsScanAux
      split
      · rename_i zero
        subst tag
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsScan) (nextData := { data with raw := raw, bitsReverse := false :: data.bitsReverse })
        · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
            (InputParserMachine.bitsScan_step_bit caller false raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx)
        · exact ih _ _
      · rename_i notZero
        split
        · rename_i one
          subst tag
          apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsScan) (nextData := { data with raw := raw, bitsReverse := true :: data.bitsReverse })
          · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
              (InputParserMachine.bitsScan_step_bit caller true raw data.rev data.pending regs
                data.outputs data.fuel data.bitsReverse ctx)
          · exact ih _ _
        · rename_i notOne
          split
          · rename_i ended
            subst tag
            apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsEmit) (nextData := { data with raw := raw })
            · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
                (InputParserMachine.bitsScan_step_end caller raw data.rev data.pending regs
                  data.outputs data.fuel data.bitsReverse ctx)
            · exact inputBitsEmit_run caller _ _ _
          · rename_i notEnd
            apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsUndo) (nextData := { data with raw := tag :: raw })
            · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
                (InputParserMachine.bitsScan_step_foreign caller tag raw data.rev data.pending regs
                  data.outputs data.fuel data.bitsReverse ctx notEnd notZero notOne)
            · exact inputBitsUndo_run caller _ _ _

theorem inputLocalFinish_run (phase : InputParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputLocalFinish phase data).Run caller (InputParserMachine.phaseLabel phase) data regs ctx := by
  cases phase with
  | sourceToRaw => exact inputSourceToRaw_run caller data regs ctx
  | sourceToReverse => exact inputSourceToReverse_run caller data regs ctx
  | restoreSep1 => exact inputRestoreSep1_run caller data regs ctx
  | targetToRaw => exact inputTargetToRaw_run caller data regs ctx
  | targetToReverse => exact inputTargetToReverse_run caller data regs ctx
  | restoreSep2 => exact inputRestoreSep2_run caller data regs ctx
  | bitsUndo => exact inputBitsUndo_run caller data regs ctx
  | fuelUndo => exact inputFuelUndo_run caller data regs ctx
  | restoreEnd => exact inputRestoreEnd_run caller data regs ctx
  | eof => exact inputEof_run caller data regs ctx
  | bitsEmit => exact inputBitsEmit_run caller data regs ctx
  | bitsScan => exact inputBitsScanAux_run caller data.raw data regs ctx

end InputExecution

def inputWithTree (data : InputState) (tree : TreeState InputParserMachine.TreeSide) : InputState :=
  { data with toTreeState := tree }

def inputTargetSuccess (data : InputState) : InputFinish :=
  match data.raw with
  | [] => inputAdd 1 (inputTargetToReverse data)
  | tag :: raw =>
      if tag = separatorTag then
        inputAdd 1 (inputBitsScanAux raw { data with raw := raw })
      else inputAdd 1 (inputTargetToReverse data)

def inputTargetTree (phase : TreeParserMachine.Phase) (data : InputState) : InputFinish :=
  let tree := treePhaseFinish .target phase data.toTreeState
  let afterTree := inputWithTree data tree.data
  inputAdd tree.steps (match tree.result with
    | .success => inputTargetSuccess afterTree
    | .failure => inputRestoreSep1 afterTree)

def inputSourceSuccess (data : InputState) : InputFinish :=
  match data.raw with
  | [] => inputAdd 1 (inputSourceToReverse data)
  | tag :: raw =>
      if tag = separatorTag then
        inputAdd 1 (inputTargetTree .init { data with raw := raw })
      else inputAdd 1 (inputSourceToReverse data)

def inputSourceTree (phase : TreeParserMachine.Phase) (data : InputState) : InputFinish :=
  let tree := treePhaseFinish .source phase data.toTreeState
  let afterTree := inputWithTree data tree.data
  match tree.result with
  | .success => inputAdd tree.steps (inputSourceSuccess afterTree)
  | .failure => ⟨.failure, afterTree, tree.steps⟩

/-- All twenty-five actual Input owned controls, including the three result handlers. -/
def inputPhaseFinish (phase : InputParserMachine.OwnedLabels) (data : InputState) : InputFinish :=
  match phase with
  | .inl (.source, phase) => inputSourceTree phase data
  | .inl (.target, phase) => inputTargetTree phase data
  | .inr (.inl .source) => inputSourceSuccess data
  | .inr (.inl .target) => inputTargetSuccess data
  | .inr (.inr (.inl _)) => inputRestoreSep1 data
  | .inr (.inr (.inr phase)) => inputLocalFinish phase data

section InputFullExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

theorem input_target_failure_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreSep1 data).Run caller (InputParserMachine.treeResultLabel .target .failure)
      data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse)
    (nextData := { data with raw := separatorTag :: data.raw })
  · exact InputParserMachine.Runs.one caller True.intro
      (InputParserMachine.target_failure_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputSourceToReverse_run caller _ _ _

theorem inputTargetSuccess_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputTargetSuccess data).Run caller (InputParserMachine.treeResultLabel .target .success)
      data regs ctx := by
  cases rawEq : data.raw with
  | nil =>
      simp only [inputTargetSuccess, rawEq]
      apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToReverse) (nextData := data)
      · apply InputParserMachine.Runs.one caller (by trivial)
        simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
          (InputParserMachine.separator_step_nil caller .target data.rev data.pending regs
            data.outputs data.fuel data.bitsReverse ctx)
      · exact inputTargetToReverse_run caller _ _ _
  | cons tag raw =>
      simp only [inputTargetSuccess, rawEq]
      split
      · rename_i separator
        subst tag
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsScan) (nextData := { data with raw := raw })
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.afterSeparator] using
            (InputParserMachine.separator_step_separator caller .target raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx)
        · exact inputBitsScanAux_run caller _ _ _ _
      · rename_i foreign
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToReverse) (nextData := data)
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
            (InputParserMachine.separator_step_foreign caller .target tag raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx foreign)
        · exact inputTargetToReverse_run caller _ _ _

theorem input_tree_segment_run (destination : InputParserMachine.TreeSide)
    (phase : TreeParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.Runs caller (treePhaseFinish destination phase data.toTreeState).steps
      (inputCfg (some (InputParserMachine.treeLabel destination phase)) regs data ctx)
      (inputCfg (some (InputParserMachine.treeResultLabel destination
        (treePhaseFinish destination phase data.toTreeState).result))
        (InputParserMachine.reset regs)
        (inputWithTree data (treePhaseFinish destination phase data.toTreeState).data) ctx) := by
  apply InputParserMachine.tree_phase_run caller
  exact treePhaseFinish_iterate (InputParserMachine.handler caller) destination phase data.toTreeState
    regs (InputParserMachine.stores data.fuel data.bitsReverse ctx)

theorem inputTargetTree_run (phase : TreeParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputTargetTree phase data).Run caller (InputParserMachine.treeLabel .target phase)
      data regs ctx := by
  unfold inputTargetTree
  apply InputFinish.Run.prepend caller (input_tree_segment_run caller .target phase data regs ctx)
  cases returned : (treePhaseFinish .target phase data.toTreeState).result with
  | success => exact inputTargetSuccess_run caller _ _ _
  | failure => exact input_target_failure_run caller _ _ _

theorem inputSourceSuccess_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputSourceSuccess data).Run caller (InputParserMachine.treeResultLabel .source .success)
      data regs ctx := by
  cases rawEq : data.raw with
  | nil =>
      simp only [inputSourceSuccess, rawEq]
      apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse) (nextData := data)
      · apply InputParserMachine.Runs.one caller (by trivial)
        simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
          (InputParserMachine.separator_step_nil caller .source data.rev data.pending regs
            data.outputs data.fuel data.bitsReverse ctx)
      · exact inputSourceToReverse_run caller _ _ _
  | cons tag raw =>
      simp only [inputSourceSuccess, rawEq]
      split
      · rename_i separator
        subst tag
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.treeLabel .target .init) (nextData := { data with raw := raw })
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.afterSeparator] using
            (InputParserMachine.separator_step_separator caller .source raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx)
        · exact inputTargetTree_run caller _ _ _ _
      · rename_i foreign
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse) (nextData := data)
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
            (InputParserMachine.separator_step_foreign caller .source tag raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx foreign)
        · exact inputSourceToReverse_run caller _ _ _

theorem inputSourceTree_run (phase : TreeParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputSourceTree phase data).Run caller (InputParserMachine.treeLabel .source phase)
      data regs ctx := by
  dsimp only [inputSourceTree]
  cases returned : (treePhaseFinish .source phase data.toTreeState).result with
  | success =>
      apply InputFinish.Run.prepend caller
      · simpa only [returned] using input_tree_segment_run caller .source phase data regs ctx
      · exact inputSourceSuccess_run caller _ _ _
  | failure =>
      simpa only [InputFinish.Run, returned, InputParserMachine.resultLabel, InputParserMachine.treeResultLabel] using input_tree_segment_run caller .source phase data regs ctx

theorem inputPhaseFinish_run (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputPhaseFinish phase data).Run caller
      (InputParserMachine.ownedLabelEquiv phase).val data regs ctx := by
  cases phase with
  | inl pair =>
      rcases pair with ⟨destination, phase⟩
      cases destination with
      | source => exact inputSourceTree_run caller phase data regs ctx
      | target => exact inputTargetTree_run caller phase data regs ctx
  | inr phase =>
      cases phase with
      | inl destination =>
          cases destination with
          | source => exact inputSourceSuccess_run caller data regs ctx
          | target => exact inputTargetSuccess_run caller data regs ctx
      | inr phase =>
          cases phase with
          | inl token => exact input_target_failure_run caller data regs ctx
          | inr phase => exact inputLocalFinish_run caller phase data regs ctx

theorem inputPhaseFinish_iterate (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (InputParserMachine.next caller)^[(inputPhaseFinish phase data).steps]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx) :=
  (inputPhaseFinish_run caller phase data regs ctx).iterate caller

theorem inputPhaseFinish_owned_prefix (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n < (inputPhaseFinish phase data).steps) :
    ∃ reached, (InputParserMachine.next caller)^[n]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached ∧ InputParserMachine.FullOwned reached.l :=
  (inputPhaseFinish_run caller phase data regs ctx).owned_prefix caller n bound

end InputFullExecution
/-! Constructive full dirty FrontEnd composition. Insert after dirty Input support. -/

inductive FrontEndMask
  | framer
  | decoder
  | input

def FrontEndMask.apply (mask : FrontEndMask) (regs : FrontEndMachine.Registers R) :
    FrontEndMachine.Registers R :=
  match mask with
  | .framer => FrontEndMachine.resetFramer regs
  | .decoder => FrontEndMachine.afterInputDecoder regs
  | .input => ((none, none), regs.2)

def frontEndMaskRegs (masks : List FrontEndMask) (regs : FrontEndMachine.Registers R) :
    FrontEndMachine.Registers R := masks.foldl (fun regs mask => mask.apply regs) regs

structure FrontEndFinish where
  result : TreeParserMachine.Result
  data : FrontEndMachine.LocalData
  steps : Nat
  masks : List FrontEndMask

def frontEndJoin (before after : FrontEndFinish) : FrontEndFinish :=
  { after with steps := before.steps + after.steps, masks := before.masks ++ after.masks }

def frontEndResultLabel (result : TreeParserMachine.Result) : FrontEndMachine.Label Λ :=
  match result with
  | .success => FrontEndMachine.dispatchLabel
  | .failure => FrontEndMachine.rejectLabel

def frontEndFinishCfg (finish : FrontEndFinish) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) : FrontEndMachine.Cfg Γ Λ R :=
  FrontEndMachine.cfg (some (frontEndResultLabel finish.result))
    (frontEndMaskRegs finish.masks regs) finish.data ctx

def frontEndInputData (data : FrontEndMachine.LocalData) : InputState :=
  { raw := data.inputRaw
    rev := data.treeReverse
    pending := data.pending
    outputs := InputParserMachine.treeOutputs data.sourceTree data.targetTree
    fuel := data.fuel
    bitsReverse := data.bitsReverse }

def frontEndWithInput (data : FrontEndMachine.LocalData) (input : InputState) :
    FrontEndMachine.LocalData :=
  { data with
    inputRaw := input.raw
    treeReverse := input.rev
    pending := input.pending
    sourceTree := input.outputs .source
    targetTree := input.outputs .target
    fuel := input.fuel
    bitsReverse := input.bitsReverse }

def frontEndInputStage (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let finish := inputPhaseFinish phase (frontEndInputData data)
  ⟨finish.result, frontEndWithInput data finish.data, finish.steps, [.input]⟩

def frontEndDecoderRaw (call : FrontEndMachine.DecoderCall) (data : FrontEndMachine.LocalData) : Bits :=
  match call with
  | .input => data.inputBits
  | .certificate => data.certificateBits

def frontEndDecoderOutput (call : FrontEndMachine.DecoderCall) (data : FrontEndMachine.LocalData) : Word :=
  match call with
  | .input => data.inputRaw
  | .certificate => data.certificateWord

def frontEndWithDecoder (call : FrontEndMachine.DecoderCall) (data : FrontEndMachine.LocalData)
    (raw : Bits) (rev out : Word) : FrontEndMachine.LocalData :=
  match call with
  | .input => { data with inputBits := raw, decodeReverse := rev, inputRaw := out }
  | .certificate => { data with certificateBits := raw, decodeReverse := rev, certificateWord := out }

def frontEndDecoderStage (call : FrontEndMachine.DecoderCall) (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let raw := frontEndDecoderRaw call data
  let rev := data.decodeReverse
  let out := frontEndDecoderOutput call data
  let steps := OpenDecoderMachine.phaseSteps phase raw rev
  match phase with
  | .emit => ⟨.success, frontEndWithDecoder call data raw [] (rev.reverse ++ out), steps, [.decoder]⟩
  | .clear => ⟨.failure, frontEndWithDecoder call data raw [] out, steps, [.decoder]⟩
  | .scan => match (unpackWordRun raw).1 with
    | none => ⟨.failure, frontEndWithDecoder call data [] [] out, steps, [.decoder]⟩
    | some word =>
        ⟨.success, frontEndWithDecoder call data [] [] (rev.reverse ++ word ++ out), steps, [.decoder]⟩

def frontEndFramerStage (phase : OpenFramingMachine.Phase) (data : FrontEndMachine.LocalData) :
    FrontEndFinish :=
  let steps := OpenFramingMachine.phaseSteps phase data.framedRaw
    data.frameFirstReverse data.frameCertReverse
  match phase with
  | .emitFirst => ⟨.success, { data with
      frameFirstReverse := []
      inputBits := data.frameFirstReverse.reverse ++ data.inputBits }, steps, [.framer]⟩
  | .clearFirst => ⟨.failure, { data with frameFirstReverse := [] }, steps, [.framer]⟩
  | .emitCert => ⟨.success, { data with
      frameFirstReverse := []
      frameCertReverse := []
      inputBits := data.frameFirstReverse.reverse ++ data.inputBits
      certificateBits := data.frameCertReverse.reverse ++ data.certificateBits }, steps, [.framer]⟩
  | .copyCert => ⟨.success, { data with
      framedRaw := []
      frameFirstReverse := []
      frameCertReverse := []
      inputBits := data.frameFirstReverse.reverse ++ data.inputBits
      certificateBits := data.frameCertReverse.reverse ++ data.framedRaw ++ data.certificateBits },
      steps, [.framer]⟩
  | .scanPrefix => match BitPairFraming.unframe data.framedRaw with
    | none => ⟨.failure, { data with framedRaw := [], frameFirstReverse := [] }, steps, [.framer]⟩
    | some pair => ⟨.success, { data with
        framedRaw := []
        frameFirstReverse := []
        frameCertReverse := []
        inputBits := data.frameFirstReverse.reverse ++ pair.1 ++ data.inputBits
        certificateBits := data.frameCertReverse.reverse ++ pair.2 ++ data.certificateBits },
        steps, [.framer]⟩

def frontEndCertificateFinish (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  frontEndDecoderStage .certificate phase data

def frontEndInputFinish (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let parsed := frontEndInputStage phase data
  match parsed.result with
  | .failure => parsed
  | .success => frontEndJoin parsed (frontEndCertificateFinish .scan parsed.data)

def frontEndInputDecoderFinish (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let decoded := frontEndDecoderStage .input phase data
  match decoded.result with
  | .failure => decoded
  | .success => frontEndJoin decoded (frontEndInputFinish (.inl (.source, .init)) decoded.data)

def frontEndFramerFinish (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let framed := frontEndFramerStage phase data
  match framed.result with
  | .failure => framed
  | .success => frontEndJoin framed (frontEndInputDecoderFinish .scan framed.data)

def frontEndPhaseFinish (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  match phase with
  | .inl phase => frontEndInputFinish phase data
  | .inr (.inl phase) => frontEndFramerFinish phase data
  | .inr (.inr (.inl phase)) => frontEndInputDecoderFinish phase data
  | .inr (.inr (.inr phase)) => frontEndCertificateFinish phase data

def frontEndPhaseSteps (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : Nat := (frontEndPhaseFinish phase data).steps

def frontEndPhaseResult (phase : FrontEndMachine.OwnedLabels)
    (regs : FrontEndMachine.Registers R) (data : FrontEndMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) : FrontEndMachine.Cfg Γ Λ R :=
  frontEndFinishCfg (frontEndPhaseFinish phase data) regs ctx

def frontEndStageCfg (success : FrontEndMachine.Label Λ) (finish : FrontEndFinish)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) : FrontEndMachine.Cfg Γ Λ R :=
  FrontEndMachine.cfg (some (match finish.result with
    | .success => success
    | .failure => FrontEndMachine.rejectLabel))
    (frontEndMaskRegs finish.masks regs) finish.data ctx

def frontEndFramerResult : TreeParserMachine.Result → OpenFramingMachine.Result
  | .success => .success
  | .failure => .failure

def frontEndDecoderResult : TreeParserMachine.Result → OpenDecoderMachine.Result
  | .success => .success
  | .failure => .failure

@[simp] theorem frontEndDecoderRaw_with (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) :
    frontEndDecoderRaw call (frontEndWithDecoder call data raw rev out) = raw := by
  cases call <;> rfl

@[simp] theorem frontEndDecoderOutput_with (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) :
    frontEndDecoderOutput call (frontEndWithDecoder call data raw rev out) = out := by
  cases call <;> rfl

@[simp] theorem frontEndWithDecoder_decodeReverse (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) :
    (frontEndWithDecoder call data raw rev out).decodeReverse = rev := by
  cases call <;> rfl

@[simp] theorem decoderContext_frontEndWithDecoder (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.decoderContext call (frontEndWithDecoder call data raw rev out) ctx =
      FrontEndMachine.decoderContext call data ctx := by
  cases call <;> rfl

@[simp] theorem inputContext_frontEndWithInput (data : FrontEndMachine.LocalData) (input : InputState)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.inputContext (frontEndWithInput data input) ctx =
      FrontEndMachine.inputContext data ctx := rfl

theorem front_end_input_outputs (input : InputState) :
    InputParserMachine.treeOutputs (input.outputs .source) (input.outputs .target) = input.outputs := by
  funext side
  cases side <;> rfl

theorem frontEndFramerStage_context (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.framerContext (frontEndFramerStage phase data).data ctx =
      FrontEndMachine.framerContext data ctx := by
  cases phase with
  | scanPrefix =>
      cases returned : BitPairFraming.unframe data.framedRaw <;>
        simp only [frontEndFramerStage, returned]
      all_goals
        funext slot
        cases slot with
        | inl slot => cases slot <;> rfl
        | inr k => rfl
  | copyCert => rfl
  | emitCert => rfl
  | emitFirst => rfl
  | clearFirst => rfl

theorem decoderRegisterEquiv_reset (regs : FrontEndMachine.Registers R) :
    FrontEndMachine.decoderRegisterEquiv
        (OpenDecoderMachine.reset (FrontEndMachine.decoderRegisterEquiv.symm regs)) =
      FrontEndMachine.afterInputDecoder regs := by
  rcases regs with ⟨tree, decoder, user⟩
  rfl

section FrontEndExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem framer_trace_transport
    (localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
      FrontEndMachine.FramerStatement Γ Λ R)
    {start finish : FrontEndMachine.FramerCfg Γ Λ R} {n : Nat}
    (executed : (OpenFramingMachine.next localCaller)^[n] (some start) = some finish)
    (owned : ∀ j, j < n → ∃ reached,
      (OpenFramingMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenFramingMachine.Owned reached.l) :
    FrontEndMachine.Trace caller (FrontEndMachine.framerCfg start)
      (FrontEndMachine.framerCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.framer_prefix_installed caller localCaller n start owned, executed]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := owned j strict
    refine ⟨FrontEndMachine.framerCfg reached, ?_, FrontEndMachine.owned_framerCfg reached isOwned⟩
    rw [FrontEndMachine.framer_prefix_installed caller localCaller j start
      (fun k smaller => owned k (by omega)), reachedEq]
    rfl

theorem input_trace_transport
    (localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
      FrontEndMachine.InputStatement Γ Λ R)
    {start finish : FrontEndMachine.InputCfg Γ Λ R} {n : Nat}
    (run : InputParserMachine.Runs localCaller n start finish) :
    FrontEndMachine.Trace caller (FrontEndMachine.inputCfg start)
      (FrontEndMachine.inputCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.input_prefix_installed caller localCaller n start
      (run.owned_prefix localCaller), run.iterate localCaller]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := run.owned_prefix localCaller j strict
    refine ⟨FrontEndMachine.inputCfg reached, ?_, FrontEndMachine.owned_inputCfg reached isOwned⟩
    rw [FrontEndMachine.input_prefix_installed caller localCaller j start
      (fun k smaller => run.owned_prefix localCaller k (by omega)), reachedEq]
    rfl

theorem input_decoder_trace_transport
    (localCaller : OpenDecoderMachine.External (FrontEndMachine.InputDecoderCaller Λ) →
      FrontEndMachine.InputDecoderStatement Γ Λ R)
    {start finish : FrontEndMachine.InputDecoderCfg Γ Λ R} {n : Nat}
    (executed : (OpenDecoderMachine.next localCaller)^[n] (some start) = some finish)
    (owned : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    FrontEndMachine.Trace caller (FrontEndMachine.inputDecoderCfg start)
      (FrontEndMachine.inputDecoderCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.input_decoder_prefix_installed caller localCaller n start owned, executed]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := owned j strict
    refine ⟨FrontEndMachine.inputDecoderCfg reached, ?_, FrontEndMachine.owned_inputDecoderCfg reached isOwned⟩
    rw [FrontEndMachine.input_decoder_prefix_installed caller localCaller j start
      (fun k smaller => owned k (by omega)), reachedEq]
    rfl

theorem certificate_decoder_trace_transport
    (localCaller : OpenDecoderMachine.External (FrontEndMachine.CertificateDecoderCaller Λ) →
      FrontEndMachine.CertificateDecoderStatement Γ Λ R)
    {start finish : FrontEndMachine.CertificateDecoderCfg Γ Λ R} {n : Nat}
    (executed : (OpenDecoderMachine.next localCaller)^[n] (some start) = some finish)
    (owned : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    FrontEndMachine.Trace caller (FrontEndMachine.certificateDecoderCfg start)
      (FrontEndMachine.certificateDecoderCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.certificate_decoder_prefix_installed caller localCaller n start owned, executed]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := owned j strict
    refine ⟨FrontEndMachine.certificateDecoderCfg reached, ?_,
      FrontEndMachine.owned_certificateDecoderCfg reached isOwned⟩
    rw [FrontEndMachine.certificate_decoder_prefix_installed caller localCaller j start
      (fun k smaller => owned k (by omega)), reachedEq]
    rfl

omit caller in
theorem frontEndFramerStage_component_iterate
    (localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
      FrontEndMachine.FramerStatement Γ Λ R)
    (phase : OpenFramingMachine.Phase) (data : FrontEndMachine.LocalData)
    (regs : OpenFramingMachine.Registers (FrontEndMachine.FramerRegisterCaller R))
    (ctx : ∀ k, List (Γ k)) :
    (OpenFramingMachine.next localCaller)^[(frontEndFramerStage phase data).steps]
      (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) regs data ctx)) =
      some (FrontEndMachine.framerView (some (OpenFramingMachine.resultLabel
        (frontEndFramerResult (frontEndFramerStage phase data).result)))
        (OpenFramingMachine.reset regs) (frontEndFramerStage phase data).data ctx) := by
  simp only [FrontEndMachine.framerView, frontEndFramerStage_context]
  cases phase with
  | scanPrefix =>
      have run := OpenFramingMachine.scanPrefix_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
      cases returned : BitPairFraming.unframe data.framedRaw <;>
        simpa only [frontEndFramerStage, OpenFramingMachine.phaseSteps,
          OpenFramingMachine.scanResult, returned, frontEndFramerResult] using run
  | copyCert =>
      exact OpenFramingMachine.copyCert_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
  | emitCert =>
      exact OpenFramingMachine.emitCert_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
  | emitFirst =>
      exact OpenFramingMachine.emitFirst_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
  | clearFirst =>
      exact OpenFramingMachine.clearFirst_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)

omit caller in
theorem frontEndDecoderStage_component_iterate {ExternalLabel : Type}
    (localCaller : OpenDecoderMachine.External ExternalLabel →
      OpenDecoderMachine.Statement (FrontEndMachine.DecoderProtectedAlphabet Γ) ExternalLabel
        (FrontEndMachine.DecoderRegisterCaller R))
    (call : FrontEndMachine.DecoderCall) (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData)
    (regs : OpenDecoderMachine.Registers (FrontEndMachine.DecoderRegisterCaller R))
    (ctx : ∀ k, List (Γ k)) :
    (OpenDecoderMachine.next localCaller)^[(frontEndDecoderStage call phase data).steps]
      (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel phase)) regs
        (frontEndDecoderRaw call data) data.decodeReverse (frontEndDecoderOutput call data)
        (FrontEndMachine.decoderContext call data ctx))) =
      some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.resultLabel
        (frontEndDecoderResult (frontEndDecoderStage call phase data).result)))
        (OpenDecoderMachine.reset regs)
        (frontEndDecoderRaw call (frontEndDecoderStage call phase data).data)
        (frontEndDecoderStage call phase data).data.decodeReverse
        (frontEndDecoderOutput call (frontEndDecoderStage call phase data).data)
        (FrontEndMachine.decoderContext call (frontEndDecoderStage call phase data).data ctx)) := by
  cases phase with
  | scan =>
      have run := OpenDecoderMachine.scan_iterate localCaller (frontEndDecoderRaw call data)
        data.decodeReverse (frontEndDecoderOutput call data) regs
        (FrontEndMachine.decoderContext call data ctx)
      cases returned : (unpackWordRun (frontEndDecoderRaw call data)).1 <;>
        simpa only [frontEndDecoderStage, OpenDecoderMachine.phaseSteps, returned,
          OpenDecoderMachine.resultCfg, frontEndDecoderResult, frontEndDecoderRaw_with,
          frontEndDecoderOutput_with, frontEndWithDecoder_decodeReverse, decoderContext_frontEndWithDecoder] using run
  | emit =>
      simpa only [frontEndDecoderStage, OpenDecoderMachine.phaseSteps, frontEndDecoderResult,
        frontEndDecoderRaw_with, frontEndDecoderOutput_with, frontEndWithDecoder_decodeReverse,
        decoderContext_frontEndWithDecoder] using
        OpenDecoderMachine.emit_iterate localCaller data.decodeReverse (frontEndDecoderRaw call data)
          (frontEndDecoderOutput call data) regs (FrontEndMachine.decoderContext call data ctx)
  | clear =>
      simpa only [frontEndDecoderStage, OpenDecoderMachine.phaseSteps, frontEndDecoderResult,
        frontEndDecoderRaw_with, frontEndDecoderOutput_with, frontEndWithDecoder_decodeReverse,
        decoderContext_frontEndWithDecoder] using
        OpenDecoderMachine.clear_iterate localCaller data.decodeReverse (frontEndDecoderRaw call data)
          (frontEndDecoderOutput call data) regs (FrontEndMachine.decoderContext call data ctx)

end FrontEndExecution

theorem frontEndFramerStage_steps (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) :
    (frontEndFramerStage phase data).steps = OpenFramingMachine.phaseSteps phase
      data.framedRaw data.frameFirstReverse data.frameCertReverse := by
  cases phase <;> simp only [frontEndFramerStage]
  split <;> rfl

theorem frontEndFramerStage_masks (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) : (frontEndFramerStage phase data).masks = [.framer] := by
  cases phase <;> simp only [frontEndFramerStage]
  split <;> rfl

theorem frontEndDecoderStage_steps (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    (frontEndDecoderStage call phase data).steps =
      OpenDecoderMachine.phaseSteps phase (frontEndDecoderRaw call data) data.decodeReverse := by
  cases phase <;> simp only [frontEndDecoderStage]
  split <;> rfl

theorem frontEndDecoderStage_masks (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    (frontEndDecoderStage call phase data).masks = [.decoder] := by
  cases phase <;> simp only [frontEndDecoderStage]
  split <;> rfl

theorem frontEndFramerResult_label (r : TreeParserMachine.Result) :
    FrontEndMachine.framerLabelEquiv
      (OpenFramingMachine.resultLabel (Λ := FrontEndMachine.FramerCaller Λ) (frontEndFramerResult r)) =
    (match r with
      | .success => FrontEndMachine.inputDecoderLabel .scan
      | .failure => FrontEndMachine.rejectLabel) := by
  cases r <;> rfl

theorem inputDecoderLabelEquiv_resultLabel (r : TreeParserMachine.Result) :
    FrontEndMachine.inputDecoderLabelEquiv
      (OpenDecoderMachine.resultLabel (Λ := FrontEndMachine.InputDecoderCaller Λ) (frontEndDecoderResult r)) =
    (match r with
      | .success => InputParserMachine.treeLabel .source .init
      | .failure => FrontEndMachine.rejectLabel) := by
  cases r <;> rfl

theorem certificateDecoderLabelEquiv_resultLabel (r : TreeParserMachine.Result) :
    FrontEndMachine.certificateDecoderLabelEquiv
      (OpenDecoderMachine.resultLabel (Λ := FrontEndMachine.CertificateDecoderCaller Λ) (frontEndDecoderResult r)) =
    frontEndResultLabel (Λ := Λ) r := by
  cases r <;> rfl

theorem inputLabelEquiv_resultLabel (r : TreeParserMachine.Result) :
    FrontEndMachine.inputLabelEquiv (InputParserMachine.resultLabel (Λ := FrontEndMachine.ExtraLabel Λ) r) =
    (match r with
      | .success => FrontEndMachine.certificateDecoderLabel .scan
      | .failure => FrontEndMachine.rejectLabel) := by
  cases r <;> rfl

theorem inputLabelEquiv_ownedLabelEquiv (phase : InputParserMachine.OwnedLabels) :
    FrontEndMachine.inputLabelEquiv
      (InputParserMachine.ownedLabelEquiv (Λ := FrontEndMachine.ExtraLabel Λ) phase).val =
        FrontEndMachine.inputOwnedLabel phase := rfl

section FrontEndStages
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEndFramerStage_trace (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
      (frontEndStageCfg (FrontEndMachine.inputDecoderLabel .scan)
        (frontEndFramerStage phase data) regs ctx) (frontEndFramerStage phase data).steps := by
  let localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
    FrontEndMachine.FramerStatement Γ Λ R := fun _ => .halt
  let localRegs := FrontEndMachine.framerRegisterEquiv.symm regs
  have executed := frontEndFramerStage_component_iterate localCaller phase data localRegs ctx
  have within : ∀ n, n < (frontEndFramerStage phase data).steps → ∃ reached,
      (OpenFramingMachine.next localCaller)^[n]
        (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx)) =
          some reached ∧ OpenFramingMachine.Owned reached.l := by
    intro n strict
    rw [frontEndFramerStage_steps] at strict
    obtain ⟨reached, reachedEq, _, _, owned, _⟩ := OpenFramingMachine.phase_prefix localCaller
      phase data.framedRaw data.frameFirstReverse data.frameCertReverse data.inputBits
      data.certificateBits localRegs (FrontEndMachine.framerContext data ctx) n (Nat.le_of_lt strict)
    exact ⟨reached, reachedEq, owned.mp strict⟩
  have translated := framer_trace_transport caller localCaller executed within
  rw [FrontEndMachine.framerCfg_view, FrontEndMachine.framerCfg_view] at translated
  simpa only [Option.map_some, FrontEndMachine.framerLabelEquiv_phase, localRegs,
    Equiv.apply_symm_apply, frontEndFramerResult_label, FrontEndMachine.framerRegisterEquiv_reset,
    frontEndStageCfg, frontEndFramerStage_masks, frontEndMaskRegs, List.foldl_cons, List.foldl_nil,
    FrontEndMask.apply] using translated

theorem frontEndInputStage_trace (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
      (frontEndStageCfg (FrontEndMachine.certificateDecoderLabel .scan)
        (frontEndInputStage phase data) regs ctx) (frontEndInputStage phase data).steps := by
  let localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
    FrontEndMachine.InputStatement Γ Λ R := fun _ => .halt
  let finish := inputPhaseFinish phase (frontEndInputData data)
  have run := inputPhaseFinish_run localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  change InputParserMachine.Runs localCaller finish.steps
    (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)
    (inputCfg (some (InputParserMachine.resultLabel finish.result))
      (InputParserMachine.reset regs) finish.data (FrontEndMachine.inputContext data ctx)) at run
  have endpoint : inputCfg (some (InputParserMachine.resultLabel (Λ := FrontEndMachine.ExtraLabel Λ) finish.result))
      (InputParserMachine.reset regs) finish.data (FrontEndMachine.inputContext data ctx) =
      FrontEndMachine.inputView (some (InputParserMachine.resultLabel finish.result))
        (InputParserMachine.reset regs) (frontEndWithInput data finish.data) ctx := by
    simp only [inputCfg, FrontEndMachine.inputView, frontEndWithInput, front_end_input_outputs]
    rfl
  rw [endpoint] at run
  have translated := input_trace_transport caller localCaller run
  rw [FrontEndMachine.inputCfg_view, FrontEndMachine.inputCfg_view] at translated
  simpa only [Option.map_some, inputLabelEquiv_resultLabel, inputLabelEquiv_ownedLabelEquiv,
    frontEndStageCfg, frontEndInputStage,
    frontEndMaskRegs, List.foldl_cons, List.foldl_nil, FrontEndMask.apply,
    FrontEndMachine.inputRegisterEquiv, Equiv.refl_apply,
    InputParserMachine.reset, TreeParserMachine.reset, finish] using translated


 theorem frontEndDecoderStage_input_trace (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
      (frontEndStageCfg (InputParserMachine.treeLabel .source .init)
        (frontEndDecoderStage .input phase data) regs ctx) (frontEndDecoderStage .input phase data).steps := by
  let localCaller : OpenDecoderMachine.External (FrontEndMachine.InputDecoderCaller Λ) →
    FrontEndMachine.InputDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
  have executed := frontEndDecoderStage_component_iterate localCaller .input phase data localRegs ctx
  have within : ∀ n, n < (frontEndDecoderStage .input phase data).steps → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[n]
        (some (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro n strict
    rw [frontEndDecoderStage_steps] at strict
    obtain ⟨reached, reachedEq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller
      phase (frontEndDecoderRaw .input data) data.decodeReverse (frontEndDecoderOutput .input data)
      localRegs (FrontEndMachine.decoderContext .input data ctx) n (Nat.le_of_lt strict)
    exact ⟨reached, reachedEq, owned.mp strict⟩
  have translated := input_decoder_trace_transport caller localCaller executed within
  change FrontEndMachine.Trace caller
    (FrontEndMachine.inputDecoderCfg (FrontEndMachine.inputDecoderView
      (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx))
    (FrontEndMachine.inputDecoderCfg (FrontEndMachine.inputDecoderView
      (some (OpenDecoderMachine.resultLabel (frontEndDecoderResult
        (frontEndDecoderStage .input phase data).result)))
      (OpenDecoderMachine.reset localRegs) (frontEndDecoderStage .input phase data).data ctx))
    (frontEndDecoderStage .input phase data).steps at translated
  rw [FrontEndMachine.inputDecoderCfg_view, FrontEndMachine.inputDecoderCfg_view] at translated
  simpa only [Option.map_some, FrontEndMachine.inputDecoderLabelEquiv_phase, localRegs,
    Equiv.apply_symm_apply, inputDecoderLabelEquiv_resultLabel, frontEndStageCfg,
    decoderRegisterEquiv_reset, frontEndDecoderStage_masks, frontEndMaskRegs,
    List.foldl_cons, List.foldl_nil, FrontEndMask.apply, FrontEndMachine.afterInputDecoder] using translated

 theorem frontEndDecoderStage_certificate_trace (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndDecoderStage .certificate phase data) regs ctx) (frontEndDecoderStage .certificate phase data).steps := by
  let localCaller : OpenDecoderMachine.External (FrontEndMachine.CertificateDecoderCaller Λ) →
    FrontEndMachine.CertificateDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
  have executed := frontEndDecoderStage_component_iterate localCaller .certificate phase data localRegs ctx
  have within : ∀ n, n < (frontEndDecoderStage .certificate phase data).steps → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[n]
        (some (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro n strict
    rw [frontEndDecoderStage_steps] at strict
    obtain ⟨reached, reachedEq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller
      phase (frontEndDecoderRaw .certificate data) data.decodeReverse (frontEndDecoderOutput .certificate data)
      localRegs (FrontEndMachine.decoderContext .certificate data ctx) n (Nat.le_of_lt strict)
    exact ⟨reached, reachedEq, owned.mp strict⟩
  have translated := certificate_decoder_trace_transport caller localCaller executed within
  change FrontEndMachine.Trace caller
    (FrontEndMachine.certificateDecoderCfg (FrontEndMachine.certificateDecoderView
      (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx))
    (FrontEndMachine.certificateDecoderCfg (FrontEndMachine.certificateDecoderView
      (some (OpenDecoderMachine.resultLabel (frontEndDecoderResult
        (frontEndDecoderStage .certificate phase data).result)))
      (OpenDecoderMachine.reset localRegs) (frontEndDecoderStage .certificate phase data).data ctx))
    (frontEndDecoderStage .certificate phase data).steps at translated
  rw [FrontEndMachine.certificateDecoderCfg_view, FrontEndMachine.certificateDecoderCfg_view] at translated
  simpa only [Option.map_some, FrontEndMachine.certificateDecoderLabelEquiv_phase, localRegs,
    Equiv.apply_symm_apply, certificateDecoderLabelEquiv_resultLabel, frontEndFinishCfg,
    decoderRegisterEquiv_reset, frontEndDecoderStage_masks, frontEndMaskRegs,
    List.foldl_cons, List.foldl_nil, FrontEndMask.apply, FrontEndMachine.afterInputDecoder] using translated

end FrontEndStages

theorem frontEndMaskRegs_append (first second : List FrontEndMask)
    (regs : FrontEndMachine.Registers R) :
    frontEndMaskRegs (first ++ second) regs = frontEndMaskRegs second (frontEndMaskRegs first regs) :=
  List.foldl_append

theorem frontEndFinishCfg_join (before after : FrontEndFinish) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    frontEndFinishCfg (Λ := Λ) (frontEndJoin before after) regs ctx =
      frontEndFinishCfg after (frontEndMaskRegs before.masks regs) ctx := by
  simp only [frontEndFinishCfg, frontEndJoin, frontEndMaskRegs_append]

theorem frontEndJoin_steps (before after : FrontEndFinish) :
    (frontEndJoin before after).steps = before.steps + after.steps := rfl

theorem frontEndFinishCfg_not_owned (finish : FrontEndFinish) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ¬ FrontEndMachine.Owned (frontEndFinishCfg (Λ := Λ) finish regs ctx).l := by
  change ¬ FrontEndMachine.Owned (some (frontEndResultLabel finish.result))
  cases finish.result with
  | success => exact FrontEndMachine.not_owned_dispatch
  | failure => exact FrontEndMachine.not_owned_reject

section FrontEndComplete
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEndInputFinish_trace (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndInputFinish phase data) regs ctx)
      (frontEndInputFinish phase data).steps := by
  have first := frontEndInputStage_trace caller phase data regs ctx
  dsimp only [frontEndInputFinish]
  cases returned : (frontEndInputStage phase data).result with
  | failure =>
      simpa only [frontEndStageCfg, frontEndFinishCfg, returned, frontEndResultLabel] using first
  | success =>
      have first' : FrontEndMachine.Trace caller
          (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
          (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel .scan))
            (frontEndMaskRegs (frontEndInputStage phase data).masks regs)
            (frontEndInputStage phase data).data ctx) (frontEndInputStage phase data).steps := by
        simpa only [frontEndStageCfg, returned] using first
      have last := frontEndDecoderStage_certificate_trace caller .scan
        (frontEndInputStage phase data).data (frontEndMaskRegs (frontEndInputStage phase data).masks regs) ctx
      change FrontEndMachine.Trace caller
        (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
        (frontEndFinishCfg (frontEndJoin (frontEndInputStage phase data)
          (frontEndCertificateFinish .scan (frontEndInputStage phase data).data)) regs ctx)
        ((frontEndInputStage phase data).steps +
          (frontEndCertificateFinish .scan (frontEndInputStage phase data).data).steps)
      rw [frontEndFinishCfg_join]
      exact first'.trans caller last

theorem frontEndInputDecoderFinish_trace (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndInputDecoderFinish phase data) regs ctx)
      (frontEndInputDecoderFinish phase data).steps := by
  have first := frontEndDecoderStage_input_trace caller phase data regs ctx
  dsimp only [frontEndInputDecoderFinish]
  cases returned : (frontEndDecoderStage .input phase data).result with
  | failure =>
      simpa only [frontEndStageCfg, frontEndFinishCfg, returned, frontEndResultLabel] using first
  | success =>
      have first' : FrontEndMachine.Trace caller
          (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
          (FrontEndMachine.cfg (some (InputParserMachine.treeLabel .source .init))
            (frontEndMaskRegs (frontEndDecoderStage .input phase data).masks regs)
            (frontEndDecoderStage .input phase data).data ctx)
          (frontEndDecoderStage .input phase data).steps := by
        simpa only [frontEndStageCfg, returned] using first
      have last := frontEndInputFinish_trace caller (.inl (.source, .init))
        (frontEndDecoderStage .input phase data).data
        (frontEndMaskRegs (frontEndDecoderStage .input phase data).masks regs) ctx
      change FrontEndMachine.Trace caller
        (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
        (frontEndFinishCfg (frontEndJoin (frontEndDecoderStage .input phase data)
          (frontEndInputFinish (.inl (.source, .init))
            (frontEndDecoderStage .input phase data).data)) regs ctx)
        ((frontEndDecoderStage .input phase data).steps +
          (frontEndInputFinish (.inl (.source, .init))
            (frontEndDecoderStage .input phase data).data).steps)
      rw [frontEndFinishCfg_join]
      exact first'.trans caller last

theorem frontEndFramerFinish_trace (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndFramerFinish phase data) regs ctx)
      (frontEndFramerFinish phase data).steps := by
  have first := frontEndFramerStage_trace caller phase data regs ctx
  dsimp only [frontEndFramerFinish]
  cases returned : (frontEndFramerStage phase data).result with
  | failure =>
      simpa only [frontEndStageCfg, frontEndFinishCfg, returned, frontEndResultLabel] using first
  | success =>
      have first' : FrontEndMachine.Trace caller
          (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
          (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel .scan))
            (frontEndMaskRegs (frontEndFramerStage phase data).masks regs)
            (frontEndFramerStage phase data).data ctx) (frontEndFramerStage phase data).steps := by
        simpa only [frontEndStageCfg, returned] using first
      have last := frontEndInputDecoderFinish_trace caller .scan
        (frontEndFramerStage phase data).data (frontEndMaskRegs (frontEndFramerStage phase data).masks regs) ctx
      change FrontEndMachine.Trace caller
        (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
        (frontEndFinishCfg (frontEndJoin (frontEndFramerStage phase data)
          (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data)) regs ctx)
        ((frontEndFramerStage phase data).steps +
          (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data).steps)
      rw [frontEndFinishCfg_join]
      exact first'.trans caller last

theorem front_end_phase_trace (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)
      (frontEndPhaseResult phase regs data ctx) (frontEndPhaseSteps phase data) := by
  cases phase with
  | inl phase => exact frontEndInputFinish_trace caller phase data regs ctx
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerFinish_trace caller phase data regs ctx
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndInputDecoderFinish_trace caller phase data regs ctx
          | inr phase =>
              cases phase with
              | scan => exact frontEndDecoderStage_certificate_trace caller .scan data regs ctx
              | emit => exact frontEndDecoderStage_certificate_trace caller .emit data regs ctx
              | clear => exact frontEndDecoderStage_certificate_trace caller .clear data regs ctx

theorem front_end_phase_iterate (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (FrontEndMachine.next caller)^[frontEndPhaseSteps phase data]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (frontEndPhaseResult phase regs data ctx) :=
  (front_end_phase_trace caller phase data regs ctx).run

theorem front_end_phase_owned_prefix (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n < frontEndPhaseSteps phase data) :
    ∃ reached, (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached ∧ FrontEndMachine.Owned reached.l :=
  (front_end_phase_trace caller phase data regs ctx).owned_prefix n bound

end FrontEndComplete



end Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd
