import Applications.Sequences.LCA.BackendBounds
import Applications.Sequences.LCA.ResidentInstallation
import Applications.Sequences.LCA.Materialize
import Applications.Sequences.LCA.PreparationScalars
import Applications.Sequences.LCA.PackingControl
import Applications.Sequences.LCA.PreparationMinima

namespace Sequences.LCA.TargetPreparation
open Resources Dijkstra.Store TreeReduction PreparationBounds PackedBackend
variable {m width : Nat}

/-- The source construction and compact output use disjoint banks. The global
word domain also contains their combined addresses and terminal loop counters. -/
theorem machine (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    BackendBounds.Machine input width (512*m) where
  words := ⟨input.positive,by have := hw.addresses; omega,hw.keys⟩
  preparation := BackendBounds.preparationPeak_le input
  query := (BackendBounds.bounds m).queryPeak input _ (Backend.prepare_valid input)

theorem eligible (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    MachineCapacity.Eligible m width (512*m) (Catalog.inputWords input)
      (Control.selectedRun (BackendBounds.sourceControl input) m).peak :=
  BackendBounds.machine_arena (machine input hw)

theorem bank_counter_fits (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    512*m < 2^width := by
  have hp := input.positive
  have hh := hw.addresses
  omega

theorem retained_fits (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    retainedSlots m ≤ 2^width :=
  (retainedSlots_le input.positive).trans (by have := hw.addresses; omega)

/-- Instantiate the finite scalar interpretation at this construction's admitted
word width. These are the class, canonical-height, sparse-span and log-loop
terminal bounds used by the source construction, before charged relocation. -/
theorem source_loop_domains (_input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) :
    2*(blockSize m-1) < 2^width ∧ blocks m < 2^width ∧
      2^(levels m) < 2^width ∧ 2^(blockSize m-1) < 2^width :=
  PreparationScalars.selected_envelopes hw

/-- Whole measured canonical and logarithm programs have finite scalar
interpretations at the exact width used by this installation. Encoding is not
an additional uncharged pass: the subsequent `sourceRun` charges conversion. -/
theorem source_scalar_refinement (_input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) (code : WordMachine.Word width) :
    TableTransport.transport (Vector.map Fin.val)
        (PreparationScalars.canonicalWord (blockSize m-1) code) =
      TableTransport.transport (Vector.map (PreparationScalars.shiftHeight (blockSize m-1)))
        (MicroExecution.canonicalM (blockSize m-1) code.val) ∧
    TableTransport.transport (Vector.map Fin.val) (PreparationScalars.logsWord width (blocks m)) =
      SparseExecution.logs (blocks m) :=
  ⟨PreparationScalars.selected_canonical hw code,PreparationScalars.selected_logs hw⟩

/-- The value is the result actually produced by measured preprocessing. The
subtype carries provenance for the finite-cell representation interpretation. -/
def rawPrepare (input : Input m) : Measured {data : Backend.State m // data = state input} Nat :=
  let r := (Backend.ops m).prepare input
  (⟨r.1,rfl⟩,r.2)

/-- Execute encoding of the actual constructed source buffers. Both source
reads and finite-word encoding operations are charged, and the resulting
resident copies have their own allocation observation. -/
def sourceRun (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :=
  bind (rawPrepare input) fun data =>
    ResidentInstallation.convertState input (eligible input hw) data.val data.property

theorem sourceRun_value (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    (sourceRun input hw).1 = ResidentInstallation.resident input (eligible input hw) := by
  simp only [sourceRun,Resources.bind,ResidentInstallation.convertState_value]
  exact ResidentInstallation.ofState_eq_resident _ _ _ _

theorem sourceRun_cost (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    (sourceRun input hw).2 ≤ 5120*m := by
  have hs := Backend.prepare_cost input
  have hc := ResidentInstallation.convertState_cost input (eligible input hw)
    (rawPrepare input).1.val (rawPrepare input).1.property
  simp only [sourceRun,Resources.bind]
  change (rawPrepare input).2 ≤ 1024*m at hs
  omega

def prepare (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    Measured (Store (512*m) (WordMachine.Word width)) Nat :=
  bind (sourceRun input hw) fun source =>
  bind (ResidentInstallation.packResident source (eligible input hw)) fun compact =>
  Materialize.install compact (retained_fits input hw) (512*m)

theorem prepare_value (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    (prepare input hw).1 = arena input (BackendBounds.machine_arena (machine input hw)) := by
  simp only [prepare,Resources.bind,sourceRun_value,ResidentInstallation.packResident_value]
  rw [Materialize.install_value _ _ _ (by
    have hh := retainedSlots_le input.positive; omega)]
  rfl

theorem prepare_cost (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :
    (prepare input hw).2 ≤ 32768*m := by
  have hs := sourceRun_cost input hw
  have hp := ResidentInstallation.packResident_linear (sourceRun input hw).1 (eligible input hw)
  have hm := Materialize.install_cost
    (ResidentInstallation.packResident (sourceRun input hw).1 (eligible input hw)).1
    (retained_fits input hw) (512*m)
  simp only [prepare,Resources.bind]
  omega

/-- Observe the actual conversion, relocation and final initialization frames.
The raw construction's frame is already counted in its source-bank peak. -/
def installControl (input : Input m) (hw : MachineCapacity.WordEligible m width (2048*m)) :=
  Control.scope [.ref input,.ref (rawPrepare input).1.val]
    (Control.seq (ResidentInstallation.convertControl (width := width) (rawPrepare input).1.val)
      fun source => Control.scope [.ref source]
        (Control.seq (PackingControl.packRun source (eligible input hw)) fun compact =>
          Control.scope [.ref compact]
            (Materialize.observeRun (Materialize.chunks compact) (by simpa only [Materialize.chunks_size] using retained_fits input hw) (512*m))))

theorem installControl_value (input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) :
    (installControl input hw).value = (prepare input hw).1 := by
  simp only [installControl,Control.scope,Control.seq,
    ResidentInstallation.convertControl_value input (eligible input hw) _ (rawPrepare input).1.property,
    PackingControl.packRun_value,Materialize.observeRun_value,prepare,sourceRun,Resources.bind,
    Materialize.install]

theorem installControl_peak (input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) :
    (installControl input hw).peak ≤ 512*m := by
  have hc := ResidentInstallation.convertControl_peak (width := width) (rawPrepare input).1.val
  have hp := PackingControl.packRun_peak
    (ResidentInstallation.convertControl (width := width) (rawPrepare input).1.val).value
    (eligible input hw)
  have hm := Materialize.observeRun_peak
    (Materialize.chunks (PackingControl.packRun
      (ResidentInstallation.convertControl (width := width) (rawPrepare input).1.val).value
      (eligible input hw)).value) (by simpa only [Materialize.chunks_size] using retained_fits input hw) (512*m)
  rw [Materialize.chunks_depth] at hm
  have hn := input.positive
  simp only [installControl,Control.scope,Control.seq,List.length_cons,List.length_nil]
  omega

/-- Retain every source allocation, converted copy and compact intermediate
until output initialization finishes. This conservative lifetime schedule
counts actual vector allocations and the observed installation frames. -/
def preparationPeak (input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) : Nat :=
  BackendBounds.preparationPeak input +
  ResidentInstallation.convertedSlots input (eligible input hw)
    (rawPrepare input).1.val (rawPrepare input).1.property +
  ResidentInstallation.allocated (sourceRun input hw).1 (eligible input hw) +
  (prepare input hw).1.toArray.size + (installControl input hw).peak

theorem preparationPeak_le (input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) :
    preparationPeak input hw ≤ 2048*m := by
  have hs := BackendBounds.preparationPeak_le input
  have hc := ResidentInstallation.convertedSlots_le input (eligible input hw)
    (rawPrepare input).1.val (rawPrepare input).1.property
  have hp := ResidentInstallation.allocated_le (sourceRun input hw).1 (eligible input hw)
  have hf := installControl_peak input hw
  simp only [preparationPeak,Vector.size_toArray]
  omega

/-- The prefix agreement required by finite within-block reads is produced by
executed relocation and initialized stores, rather than assumed of raw buffers. -/
theorem prepare_prefix (input : Input m)
    (hw : MachineCapacity.WordEligible m width (2048*m)) :
    PreparationMinima.PrefixAgrees (m := m) (prepare input hw).1
      (arena input (eligible input hw)) := by
  rw [prepare_value]
  intro i hi
  rfl

/-- The compact bank starts at zero, so its checked local descriptor values
are also global machine addresses. Source construction lives in a separate
bank; compaction cannot overwrite any still-live input buffer. -/
def outputSegment (m : Nat) : Arena.Segment (2048*m) (512*m) := ⟨0,by omega⟩
def sourceSegment (m : Nat) : Arena.Segment (2048*m) (512*m) := ⟨512*m,by omega⟩

theorem banks_disjoint (m : Nat) : Arena.Disjoint (outputSegment m) (sourceSegment m) :=
  Or.inl (by simp [outputSegment,sourceSegment])

theorem output_write_preserves_source (source : Store (512*m) (WordMachine.Word width))
    (memory : Store (2048*m) (WordMachine.Word width))
    (hr : Arena.Represents (sourceSegment m) source memory)
    (i : Fin (512*m)) (value : WordMachine.Word width) :
    Arena.Represents (sourceSegment m) source
      (write memory ((outputSegment m).address i) value) :=
  Arena.other_segment_preserved _ _ (banks_disjoint m) source memory hr i value

theorem source_bank_address_fits (hw : MachineCapacity.WordEligible m width (2048*m))
    (i : Fin (512*m)) : ((sourceSegment m).address i).val < 2^width :=
  MachineCapacity.address_fits hw _

def convertedSegment (m : Nat) : Arena.Segment (2048*m) (128*m) := ⟨1024*m,by omega⟩
def packedSegment (m : Nat) : Arena.Segment (2048*m) (64*m) := ⟨1152*m,by omega⟩
def controlSegment (m : Nat) : Arena.Segment (2048*m) (512*m) := ⟨1216*m,by omega⟩

theorem output_converted_disjoint (m : Nat) : Arena.Disjoint (outputSegment m) (convertedSegment m) :=
  Or.inl (by simp [outputSegment,convertedSegment]; omega)
theorem output_packed_disjoint (m : Nat) : Arena.Disjoint (outputSegment m) (packedSegment m) :=
  Or.inl (by simp [outputSegment,packedSegment]; omega)
theorem source_converted_disjoint (m : Nat) : Arena.Disjoint (sourceSegment m) (convertedSegment m) :=
  Or.inl (by simp [sourceSegment,convertedSegment]; omega)
theorem converted_packed_disjoint (m : Nat) : Arena.Disjoint (convertedSegment m) (packedSegment m) :=
  Or.inl (by simp [convertedSegment,packedSegment]; omega)
theorem packed_control_disjoint (m : Nat) : Arena.Disjoint (packedSegment m) (controlSegment m) :=
  Or.inl (by simp [packedSegment,controlSegment]; omega)

/-- The complete still-live source and temporary region is outside the output
bank, including converted cells, compact intermediate buffers and control. -/
def workspaceSegment (m : Nat) : Arena.Segment (2048*m) (1536*m) := ⟨512*m,by omega⟩

theorem output_workspace_disjoint (m : Nat) : Arena.Disjoint (outputSegment m) (workspaceSegment m) :=
  Or.inl (by simp [outputSegment,workspaceSegment])

theorem output_write_preserves_workspace (workspace : Store (1536*m) (WordMachine.Word width))
    (memory : Store (2048*m) (WordMachine.Word width))
    (hr : Arena.Represents (workspaceSegment m) workspace memory)
    (i : Fin (512*m)) (value : WordMachine.Word width) :
    Arena.Represents (workspaceSegment m) workspace
      (write memory ((outputSegment m).address i) value) :=
  Arena.other_segment_preserved _ _ (output_workspace_disjoint m) workspace memory hr i value

theorem output_install_preserves_workspace (output : Store (512*m) (WordMachine.Word width))
    (workspace : Store (1536*m) (WordMachine.Word width))
    (memory : Store (2048*m) (WordMachine.Word width))
    (hr : Arena.Represents (workspaceSegment m) workspace memory) :
    Arena.Represents (workspaceSegment m) workspace
      (Arena.install (outputSegment m) output memory) :=
  Arena.install_other _ _ (output_workspace_disjoint m) output workspace memory hr

theorem source_packed_disjoint (m : Nat) : Arena.Disjoint (sourceSegment m) (packedSegment m) :=
  Or.inl (by simp [sourceSegment,packedSegment]; omega)

theorem conversion_write_preserves_source (source : Store (512*m) (WordMachine.Word width))
    (memory : Store (2048*m) (WordMachine.Word width))
    (hr : Arena.Represents (sourceSegment m) source memory)
    (i : Fin (128*m)) (value : WordMachine.Word width) :
    Arena.Represents (sourceSegment m) source
      (write memory ((convertedSegment m).address i) value) :=
  Arena.other_segment_preserved _ _ (Or.inr (by simp [sourceSegment,convertedSegment]; omega)) source memory hr i value

theorem packing_write_preserves_converted (source : Store (128*m) (WordMachine.Word width))
    (memory : Store (2048*m) (WordMachine.Word width))
    (hr : Arena.Represents (convertedSegment m) source memory)
    (i : Fin (64*m)) (value : WordMachine.Word width) :
    Arena.Represents (convertedSegment m) source
      (write memory ((packedSegment m).address i) value) :=
  Arena.other_segment_preserved _ _ (Or.inr (by simp [convertedSegment,packedSegment]; omega)) source memory hr i value

end Sequences.LCA.TargetPreparation
