import Applications.Sequences.LCA.Installation
import Applications.Sequences.LCA.PreparationCertificate

/-! Compact resident source buffers into the descriptor-bearing retained
representation. Scalar fields remain aliases; shared and macro tables execute
the charged relocation programs. -/
namespace Sequences.LCA.ResidentInstallation
open Resources PreparationBounds PackedBackend TreeReduction PreparationCertificate
variable {m width capacity inputWords frameWords : Nat}

structure Resident (m width : Nat) where
  depths : Vector (WordMachine.Word width) (blocks m*(blockSize m-1+1))
  classes : Vector (WordMachine.Word width) (blocks m)
  shared : Vector (Vector (Vector (WordMachine.Word width) (blockSize m-1+1))
    (blockSize m-1+1)) (2^(blockSize m-1))
  macroRows : Vector (Vector (WordMachine.Word width) (blocks m)) (levels m+1)
  spans : Vector (WordMachine.Word width) (levels m+1)
  logs : Vector (WordMachine.Word width) (blocks m+1)

theorem sharedFits (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    paddedCapacity m+blocks m+
      FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) ≤ capacity := by
  rw [FlatTable.sharedPack_size,dimension]
  have hh := h.memory
  unfold MachineCapacity.requiredSlots retainedSlots sharedSlots at hh
  omega

def packResident (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    Measured (Representation m width) Nat :=
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  bind (Installation.sharedM (blockSize m-1) r.shared (paddedCapacity m+blocks m) capacity
    (sharedFits h) h.addresses) fun shared =>
  bind (Installation.packM r.macroRows (macroBase m) capacity (macro_fit h) h.addresses) fun packedMacro =>
  pure ⟨r.depths,r.classes,shared,packedMacro,r.spans,r.logs⟩

/-- This view selects the finite buffers produced by the checked preparation
programs. Mapping into the selected width is the interpretation of their cell
representation, not an uncharged runtime conversion pass. -/
def resident (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : Resident m width where
  depths := depthWords input h.toWordEligible
  classes := classWords input h.toWordEligible
  shared := (sharedProgram (blockSize m-1)).1.map
    (Vector.map (Vector.map (widen (micro_width input h.toWordEligible))))
  macroRows := (wideMacroProgram input h.toWordEligible).1.1.map Prod.fst
  spans := spanWords input h.toWordEligible
  logs := logWords input h.toWordEligible

theorem resident_shared (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) :
    (resident input h).shared[code.val] = FlatTable.microMatrix code (micro_width input h.toWordEligible) := by
  apply Vector.ext
  intro start hs
  apply Vector.ext
  intro len hl
  simp only [resident,Vector.getElem_map]
  have hh := sharedProgram_physical input h code ⟨start,hs⟩ ⟨len,hl⟩
  unfold sharedWords at hh
  rw [FlatTable.sharedPack_payload] at hh
  exact hh

theorem resident_macro (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (resident input h).macroRows = macroWords input h.toWordEligible := by
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  apply Vector.ext
  intro level hlevel
  apply Vector.ext
  intro i hi
  simp only [resident,wideMacroProgram_refines,TableTransport.transport,TableTransport.rowsMap,Vector.getElem_map]
  have hh := macroProgram_physical input h ⟨level,hlevel⟩ ⟨i,hi⟩
  unfold macroPack at hh
  rw [FlatTable.payload_read] at hh
  exact hh

theorem packResident_value (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (packResident (resident input h) h).1 = realize input h := by
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  simp only [packResident,Resources.bind,Resources.pure]
  rw [Installation.sharedM_value _ _ (micro_width input h.toWordEligible) (resident_shared input h),
    Installation.packM_value,resident_macro]
  rfl

def installWork (m : Nat) :=
  3*FlatTable.words (blockSize m) (blockSize m)+
    2^(blockSize m-1)*(12*FlatTable.words (blockSize m) (blockSize m)+10)+
    12*sharedSlots m+12*FlatTable.words (levels m+1) (blocks m)

theorem packResident_cost (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (packResident r h).2 ≤ installWork m := by
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  have hs := Installation.sharedM_cost (blockSize m-1) r.shared (sharedFits h) h.addresses
  have hm := Installation.packM_cost r.macroRows (macro_fit h) h.addresses
  simp only [packResident,Resources.bind,Resources.pure]
  simp only [FlatTable.sharedPack_size,dimension] at hs
  change _ ≤ installWork m
  have he : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m) (blockSize m)) = sharedSlots m := by
    unfold FlatTable.words sharedSlots; ring
  unfold installWork
  omega

/-- Representation of the supplied executed source state. Every runtime
field is read from `data`; the equality witness only discharges word bounds. -/
def ofState (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) : Resident m width where
  depths := Vector.ofFn fun i => ⟨data.micro.depths[i.val].toNat,by
    rw [valid]
    simpa only [depthWords,Vector.getElem_ofFn] using ((depthWords input h.toWordEligible)[i.val]).isLt⟩
  classes := data.micro.classes.map fun code => ⟨code.val,code.isLt.trans (MachineCapacity.class_count_fits h.toWordEligible)⟩
  shared := Vector.ofFn fun code => Vector.ofFn fun start => Vector.ofFn fun len =>
    ⟨WordKey.encode ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1))
      (ofLex data.micro.shared[code.val][start.val][len.val]).1
      (ofLex data.micro.shared[code.val][start.val][len.val]).2,by
        rw [valid]
        have hh := sharedWords_read input h code start len
        have hw := ((sharedWords input h)[2^(blockSize m-1)+
          code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
          ((blockSize m-1+1)+start.val*(blockSize m-1+1)+len.val)]'
          (FlatTable.payload_index_lt code ⟨_,FlatTable.payload_index_lt start len⟩)).isLt
        rw [hh] at hw
        exact hw⟩
  macroRows := Vector.ofFn fun level => Vector.ofFn fun i =>
    ⟨WordKey.encode 0 (blocks m*(blockSize m-1+1))
      (ofLex (data.macroRows[level.val]).1[i.val]).1
      (ofLex (data.macroRows[level.val]).1[i.val]).2,by
        rw [valid,← macroWords_read input h.toWordEligible level i]
        exact ((macroWords input h.toWordEligible)[level.val][i.val]).isLt⟩
  spans := Vector.ofFn fun level => ⟨(data.macroRows[level.val]).2,by
    rw [valid,← spanWords_read input h.toWordEligible level]
    exact ((spanWords input h.toWordEligible)[level.val]).isLt⟩
  logs := Vector.ofFn fun i => ⟨data.macroLogs[i.val],by
    rw [valid,← logWords_read input h.toWordEligible i]
    exact ((logWords input h.toWordEligible)[i.val]).isLt⟩

theorem ofState_eq_resident (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    ofState input h data valid = resident input h := by
  subst data
  have hs : (ofState input h (state input) rfl).shared = (resident input h).shared := by
    apply Vector.ext
    intro code hc
    rw [resident_shared input h ⟨code,hc⟩]
    apply Vector.ext
    intro start hstart
    apply Vector.ext
    intro len hlen
    apply Fin.ext
    simp only [ofState,Vector.getElem_ofFn]
    have hx := sharedWords_read input h ⟨code,hc⟩ ⟨start,hstart⟩ ⟨len,hlen⟩
    have hy := FlatTable.sharedPack_payload (blockSize m-1) (paddedCapacity m+blocks m) capacity
      (micro_width input h.toWordEligible) (shared_fit input h) h.addresses ⟨code,hc⟩ ⟨start,hstart⟩ ⟨len,hlen⟩
    exact hx.symm.trans (congrArg Fin.val hy)
  have hm : (ofState input h (state input) rfl).macroRows = (resident input h).macroRows := by
    rw [resident_macro]
    apply Vector.ext
    intro level hl
    apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [ofState,Vector.getElem_ofFn]
    exact (macroWords_read input h.toWordEligible ⟨level,hl⟩ ⟨i,hi⟩).symm
  change Resident.mk _ _ _ _ _ _ = Resident.mk _ _ _ _ _ _
  congr 1 <;> first | exact hs | exact hm | rfl

theorem innerWords_le_shared (m : Nat) :
    FlatTable.words (blockSize m) (blockSize m) ≤ sharedSlots m := by
  have hc : 1 ≤ 2^(blockSize m-1) := Nat.one_le_pow _ _ (by decide)
  have hh := Nat.mul_le_mul_right (blockSize m*blockSize m+blockSize m+1) hc
  unfold FlatTable.words sharedSlots
  nlinarith

theorem macroWords_le (hn : 0 < m) : FlatTable.words (levels m+1) (blocks m) ≤ 26*m := by
  have hs := sparseSlots_le hn
  unfold FlatTable.words SparseExecution.retainedSlots at *
  nlinarith

theorem installWork_le (hn : 0 < m) : installWork m ≤ 512*m := by
  have hn' := innerWords_le_shared m
  have hs := sharedSlots_le hn
  have hm := macroWords_le hn
  have he : 2^(blockSize m-1)*(12*FlatTable.words (blockSize m) (blockSize m)+10) ≤ 12*sharedSlots m := by
    have heq : 2^(blockSize m-1)*(12*FlatTable.words (blockSize m) (blockSize m)+10)+2*2^(blockSize m-1) = 12*sharedSlots m := by
      unfold FlatTable.words sharedSlots; ring
    omega
  unfold installWork
  omega

/-- Sizes of buffers constructed by the actual two relocation programs,
including shared compaction intermediates and both retained table outputs.
The resident input is additional; scalar fields are aliased. -/
def allocated (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : Nat :=
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  Installation.tensorSlotsObserved r.shared (paddedCapacity m+blocks m) capacity (sharedFits h) h.addresses +
    (Installation.packM r.macroRows (macroBase m) capacity (macro_fit h) h.addresses).1.toArray.size

theorem allocated_eq (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    allocated r h = FlatTable.words (blockSize m) (blockSize m)+2*sharedSlots m+
      FlatTable.words (levels m+1) (blocks m) := by
  simp only [allocated,Installation.tensorSlotsObserved_eq,Vector.size_toArray,Installation.tensorAllocation,dimension]
  unfold FlatTable.words sharedSlots
  ring

theorem allocated_le (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : allocated r h ≤ 64*m := by
  rw [allocated_eq]
  have hn := innerWords_le_shared m
  have hs := sharedSlots_le h.positive
  have hm := macroWords_le h.positive
  omega

theorem packResident_linear (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : (packResident r h).2 ≤ 512*m :=
  (packResident_cost r h).trans (installWork_le h.positive)

section InstallationControl
variable {rows cols base : Nat} [NeZero cols]

/-- Retain the arguments and every produced scalar/reference for one
installation cell. These are the arithmetic and read results of its branch;
no recursive or source buffer payload is copied into this frame. -/
def cellControl (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin (FlatTable.words rows cols)) : Control.Run (WordMachine.Word width) :=
  if hi : i.val<rows then
    let product := (WordMachine.scalar width (i.val*cols)).1
    let relative := (WordMachine.scalar width (rows+product.val)).1
    let address := (WordMachine.scalar width (base+relative.val)).1
    Control.note address [.ref cells,.nat base,.nat capacity,.nat rows,.nat cols,.nat i.val,
      .bit true,.ref product,.ref relative,.ref address]
  else
    let pos := i.val-rows
    let row : Fin rows := ⟨pos/cols,(Nat.div_lt_iff_lt_mul (NeZero.pos cols)).2 (by
      have hh := i.isLt; unfold FlatTable.words at hh; omega)⟩
    let col : Fin cols := ⟨pos%cols,Nat.mod_lt _ (NeZero.pos cols)⟩
    let resident := (TableExecution.read cells row).1
    let word := (TableExecution.read resident col).1
    Control.note word [.ref cells,.nat base,.nat capacity,.nat rows,.nat cols,.nat i.val,
      .bit false,.nat pos,.nat row.val,.nat col.val,.ref resident,.ref word]

theorem cellControl_value (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin (FlatTable.words rows cols)) :
    (cellControl cells fit wide i).value = (Installation.packCell cells base capacity fit wide i).1 := by
  by_cases hi : i.val<rows
  · simp only [cellControl,hi,dite_true,Control.note,Installation.packCell]
    rfl
  · rw [Installation.packCell_value]
    let row : Fin rows := ⟨(i.val-rows)/cols,(Nat.div_lt_iff_lt_mul (NeZero.pos cols)).2 (by
      have hh := i.isLt; unfold FlatTable.words at hh; omega)⟩
    let col : Fin cols := ⟨(i.val-rows)%cols,Nat.mod_lt _ (NeZero.pos cols)⟩
    have he : rows+row.val*cols+col.val=i.val := by
      have hh : (i.val-rows)/cols*cols+(i.val-rows)%cols=i.val-rows := by
        simpa [Nat.mul_comm] using Nat.div_add_mod (i.val-rows) cols
      dsimp [row,col]
      omega
    have hh := FlatTable.payload_read cells fit wide row col
    simpa only [cellControl,hi,dite_false,Control.note,TableExecution.read,Dijkstra.Store.lookup,he] using hh.symm

theorem cellControl_peak (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin (FlatTable.words rows cols)) : (cellControl cells fit wide i).peak ≤ 12 := by
  unfold cellControl
  split <;> simp [Control.note]

def packControl (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :=
  Control.tabulate (WordMachine.word width 0) (cellControl cells fit wide)

theorem packControl_value (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :
    (packControl cells fit wide).value = (Installation.packM cells base capacity fit wide).1 := by
  simp only [packControl,Control.tabulate_value,cellControl_value,Installation.packM,TableExecution.tabulate_value]

theorem packControl_peak (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :
    (packControl cells fit wide).peak ≤ 20 :=
  Control.tabulate_peak _ _ (cellControl_peak cells fit wide)
end InstallationControl

end Sequences.LCA.ResidentInstallation
