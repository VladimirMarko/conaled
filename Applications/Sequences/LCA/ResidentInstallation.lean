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

/-- Radix conversion executes the shifted height and index materialization,
then multiplication and addition. All four scalar instructions are charged. -/
def keyM (offset : Int) (stride : Nat) (key : KeyBounds.Key) : Measured (WordMachine.Word width) Nat :=
  bind (WordMachine.scalar width ((ofLex key).1+offset).toNat) fun height =>
  bind (WordMachine.scalar width (ofLex key).2) fun index =>
  WordMachine.pack stride height index

theorem keyM_value (hs : 0 < stride)
    (hw : WordKey.encode offset stride (ofLex key).1 (ofLex key).2 < 2^width) :
    (keyM (width := width) offset stride key).1.val =
      WordKey.encode offset stride (ofLex key).1 (ofLex key).2 := by
  have hm := Nat.le_mul_of_pos_right ((ofLex key).1+offset).toNat hs
  have hheight : ((ofLex key).1+offset).toNat < 2^width := by unfold WordKey.encode WordKey.pack at hw; omega
  have hindex : (ofLex key).2 < 2^width := by unfold WordKey.encode WordKey.pack at hw; omega
  have hp : ((ofLex key).1+offset).toNat*stride < 2^width := by unfold WordKey.encode WordKey.pack at hw; omega
  simp only [keyM,Resources.bind,WordMachine.pack,WordMachine.scalar]
  rw [WordMachine.word_of_lt hheight,WordMachine.word_of_lt hindex,
    WordMachine.word_of_lt hp]
  exact WordMachine.word_of_lt hw

def mapM (seed : β) (f : α → Measured β Nat) (source : Vector α n) :=
  TableExecution.tabulate seed (fun i : Fin n => bind (TableExecution.read source i) f)

theorem mapM_value (seed : β) (f : α → Measured β Nat) (source : Vector α n) :
    (mapM seed f source).1 = source.map (fun x => (f x).1) := by
  rw [mapM,TableExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn,Vector.getElem_map,Resources.bind,TableExecution.read,Dijkstra.Store.lookup]

theorem mapM_cost (seed : β) (f : α → Measured β Nat) (source : Vector α n)
    (hc : ∀ x, (f x).2 ≤ c) : (mapM seed f source).2 ≤ n*(c+7) := by
  have hh := TableExecution.tabulate_cost seed
    (fun i : Fin n => bind (TableExecution.read source i) f) (c+1)
    (fun i => by simp only [Resources.bind,TableExecution.read]; have hh := hc (Dijkstra.Store.lookup source i); omega)
  simpa [mapM,Nat.add_assoc] using hh

def rowM (offset : Int) (stride : Nat) (source : Vector KeyBounds.Key n) :=
  mapM (WordMachine.word width 0) (keyM offset stride) source

def matrixM (offset : Int) (stride : Nat) (source : Vector (Vector KeyBounds.Key cols) rows) :=
  bind (TableExecution.initStore (WordMachine.word width 0) cols) fun seed =>
  mapM seed (rowM offset stride) source

def tensorM (offset : Int) (stride : Nat)
    (source : Vector (Vector (Vector KeyBounds.Key cols) rows) classes) :=
  bind (TableExecution.initStore (WordMachine.word width 0) cols) fun rowSeed =>
  bind (TableExecution.initStore rowSeed rows) fun classSeed =>
  mapM classSeed (matrixM offset stride) source

def convertState (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (_valid : data = PackedBackend.state input) : Measured (Resident m width) Nat :=
  bind (mapM (WordMachine.word width 0) (fun d : Int => WordMachine.scalar width d.toNat) data.micro.depths) fun depths =>
  bind (mapM (WordMachine.word width 0) (fun c : Fin (2^(blockSize m-1)) => WordMachine.scalar width c.val) data.micro.classes) fun classes =>
  bind (tensorM ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1)) data.micro.shared) fun shared =>
  bind (TableExecution.initStore (WordMachine.word width 0) (blocks m)) fun seed =>
  bind (mapM seed (fun desc : Vector KeyBounds.Key (blocks m) × Nat => rowM 0 (blocks m*(blockSize m-1+1)) desc.1) data.macroRows) fun macroRows =>
  bind (mapM (WordMachine.word width 0) (fun desc : Vector KeyBounds.Key (blocks m) × Nat => WordMachine.scalar width desc.2) data.macroRows) fun spans =>
  bind (mapM (WordMachine.word width 0) (WordMachine.scalar width) data.macroLogs) fun logs =>
  pure ⟨depths,classes,shared,macroRows,spans,logs⟩

theorem convertState_value (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    (convertState input h data valid).1 = ofState input h data valid := by
  simp only [convertState,Resources.bind,Resources.pure,tensorM,matrixM,rowM,mapM_value,
    TableExecution.initStore_exact,ofState]
  congr 1
  · apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact WordMachine.word_of_lt (by simpa only [ofState,Vector.getElem_ofFn,Vector.getElem_map] using ((ofState input h data valid).depths[i]).isLt)
  · apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Vector.getElem_map]
    exact WordMachine.word_of_lt (by simpa only [ofState,Vector.getElem_ofFn,Vector.getElem_map] using ((ofState input h data valid).classes[i]).isLt)
  · apply Vector.ext
    intro code hc
    apply Vector.ext
    intro start hs
    apply Vector.ext
    intro len hl
    apply Fin.ext
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact keyM_value (by have := blockSize_pos m; omega)
      (by simpa only [ofState,Vector.getElem_ofFn,Vector.getElem_map] using ((ofState input h data valid).shared[code][start][len]).isLt)
  · apply Vector.ext
    intro level hl
    apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact keyM_value (Nat.mul_pos (blocks_pos m) (by omega))
      (by simpa only [ofState,Vector.getElem_ofFn,Vector.getElem_map] using ((ofState input h data valid).macroRows[level][i]).isLt)
  · apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact WordMachine.word_of_lt (by simpa only [ofState,Vector.getElem_ofFn,Vector.getElem_map] using ((ofState input h data valid).spans[i]).isLt)
  · apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact WordMachine.word_of_lt (by simpa only [ofState,Vector.getElem_ofFn,Vector.getElem_map] using ((ofState input h data valid).logs[i]).isLt)

theorem rowM_cost (offset : Int) (stride : Nat) (source : Vector KeyBounds.Key n) :
    (rowM (width := width) offset stride source).2 ≤ 11*n := by
  simpa [rowM,Nat.mul_comm] using mapM_cost (WordMachine.word width 0) (keyM offset stride) source (c := 4) (fun _ => le_rfl)

theorem matrixM_cost (offset : Int) (stride : Nat) (source : Vector (Vector KeyBounds.Key cols) rows) :
    (matrixM (width := width) offset stride source).2 ≤ 3*cols+rows*(11*cols+7) := by
  have hh := mapM_cost (TableExecution.initStore (WordMachine.word width 0) cols).1
    (rowM offset stride) source (rowM_cost offset stride)
  simp only [matrixM,Resources.bind,TableExecution.initStore_exact]
  simp only [TableExecution.initStore_exact] at hh
  omega

theorem tensorM_cost (offset : Int) (stride : Nat)
    (source : Vector (Vector (Vector KeyBounds.Key cols) rows) classes) :
    (tensorM (width := width) offset stride source).2 ≤
      3*cols+3*rows+classes*(3*cols+rows*(11*cols+7)+7) := by
  have hh := mapM_cost
    (TableExecution.initStore (TableExecution.initStore (WordMachine.word width 0) cols).1 rows).1
    (matrixM offset stride) source (matrixM_cost offset stride)
  simp only [tensorM,Resources.bind,TableExecution.initStore_exact]
  simp only [TableExecution.initStore_exact] at hh
  omega

def convertWork (m : Nat) :=
  8*paddedCapacity m+8*blocks m+
  (6*blockSize m+2^(blockSize m-1)*(3*blockSize m+blockSize m*(11*blockSize m+7)+7))+
  3*blocks m+(levels m+1)*(11*blocks m+7)+8*(levels m+1)+8*(blocks m+1)

theorem convertState_work (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    (convertState input h data valid).2 ≤ convertWork m := by
  have hd := mapM_cost (WordMachine.word width 0) (fun d : Int => WordMachine.scalar width d.toNat)
    data.micro.depths (c := 1) (fun _ => le_rfl)
  have hc := mapM_cost (WordMachine.word width 0) (fun c : Fin (2^(blockSize m-1)) => WordMachine.scalar width c.val)
    data.micro.classes (c := 1) (fun _ => le_rfl)
  have ht := tensorM_cost (width := width) ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1)) data.micro.shared
  have hm := mapM_cost (TableExecution.initStore (WordMachine.word width 0) (blocks m)).1
    (fun desc : Vector KeyBounds.Key (blocks m) × Nat => rowM 0 (blocks m*(blockSize m-1+1)) desc.1)
    data.macroRows (fun desc => rowM_cost 0 _ desc.1)
  have hs := mapM_cost (WordMachine.word width 0)
    (fun desc : Vector KeyBounds.Key (blocks m) × Nat => WordMachine.scalar width desc.2)
    data.macroRows (c := 1) (fun _ => le_rfl)
  have hl := mapM_cost (WordMachine.word width 0) (WordMachine.scalar width) data.macroLogs (c := 1) (fun _ => le_rfl)
  simp only [convertState,Resources.bind,Resources.pure,TableExecution.initStore_exact]
  simp only [dimension,TableExecution.initStore_exact] at hd ht hm ⊢
  unfold convertWork paddedCapacity
  omega

theorem convertWork_le (hn : 0 < m) : convertWork m ≤ 4096*m := by
  have hp := paddedCapacity_le hn
  have hk := blocks_le hn
  have hb := blockSize_le hn
  have hs := sharedSlots_le hn
  have hsp := sparseSlots_le hn
  have ht : 2^(blockSize m-1)*(3*blockSize m+blockSize m*(11*blockSize m+7)+7) ≤ 11*sharedSlots m := by
    have he : 2^(blockSize m-1)*(3*blockSize m+blockSize m*(11*blockSize m+7)+7)+
        2^(blockSize m-1)*(blockSize m+4)=11*sharedSlots m := by unfold sharedSlots; ring
    omega
  have hmacro : (levels m+1)*(11*blocks m+7)+8*(levels m+1) ≤
      26*SparseExecution.retainedSlots (blocks m) (levels m) := by
    unfold SparseExecution.retainedSlots
    nlinarith
  unfold convertWork
  omega

theorem convertState_cost (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    (convertState input h data valid).2 ≤ 4096*m :=
  (convertState_work input h data valid).trans (convertWork_le input.positive)

/-- Count the actual converted payload vectors, pointer vectors, and the
zero-seed vectors allocated by the nested conversion loops. -/
def convertedSlots (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) : Nat :=
  let r := (convertState input h data valid).1
  r.depths.toArray.size+r.classes.toArray.size+r.shared.toArray.size+
    (∑ c : Fin (2^(blockSize m-1)), (r.shared[c.val].toArray.size+
      ∑ i : Fin (blockSize m-1+1), r.shared[c.val][i.val].toArray.size))+
    r.macroRows.toArray.size+(∑ i : Fin (levels m+1), r.macroRows[i.val].toArray.size)+
    r.spans.toArray.size+r.logs.toArray.size+
    2*(TableExecution.initStore (WordMachine.word width 0) (blockSize m-1+1)).1.toArray.size+
    (∑ _c : Fin (2^(blockSize m-1)),
      (TableExecution.initStore (WordMachine.word width 0) (blockSize m-1+1)).1.toArray.size)+
    (TableExecution.initStore (WordMachine.word width 0) (blocks m)).1.toArray.size

theorem convertedSlots_eq (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    convertedSlots input h data valid = retainedSlots m+2*blockSize m+2^(blockSize m-1)*blockSize m := by
  simp only [convertedSlots,Vector.size_toArray,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,dimension]
  unfold retainedSlots paddedCapacity sharedSlots SparseExecution.retainedSlots
  ring

theorem convertedSlots_le (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    convertedSlots input h data valid ≤ 128*m := by
  rw [convertedSlots_eq]
  have hr := retainedSlots_le h.positive
  have hb := blockSize_le h.positive
  have hs := sharedSlots_le h.positive
  have hc : 2^(blockSize m-1)*blockSize m ≤ sharedSlots m := by
    unfold sharedSlots
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- Decode a resident packed source word using quotient and remainder, then
repack it. This is the finite-word interpretation of the two projections in
`keyM`; it has exactly the same four scalar instructions. -/
def repackM (stride : Nat) (source : WordMachine.Word width) :=
  bind (WordMachine.scalar width (source.val/stride)) fun height =>
  bind (WordMachine.scalar width (source.val%stride)) fun index =>
  WordMachine.pack stride height index

theorem repackM_keyM (offset : Int) (stride : Nat) (key : KeyBounds.Key)
    (hi : (ofLex key).2 < stride)
    (hw : WordKey.encode offset stride (ofLex key).1 (ofLex key).2 < 2^width) :
    repackM stride (⟨WordKey.encode offset stride (ofLex key).1 (ofLex key).2,hw⟩ : WordMachine.Word width) =
      keyM offset stride key := by
  simp only [repackM,keyM,WordKey.encode,WordKey.pack_div hi,WordKey.pack_mod hi]

theorem repackM_cost (stride : Nat) (source : WordMachine.Word width) :
    (repackM stride source).2 = 4 := rfl

/-- A conversion callback retains its arguments and the four actual arithmetic
results. The packed source key occupies one reference slot. -/
def keyControl (offset : Int) (stride : Nat) (key : KeyBounds.Key) :
    Control.Run (WordMachine.Word width) :=
  let height := (WordMachine.scalar width ((ofLex key).1+offset).toNat).1
  let index := (WordMachine.scalar width (ofLex key).2).1
  let product := (WordMachine.scalar width (height.val*stride)).1
  let result := (WordMachine.scalar width (product.val+index.val)).1
  Control.note result [.integer offset,.nat stride,.ref key,.ref height,.ref index,.ref product,.ref result]

theorem keyControl_value : (keyControl (width := width) offset stride key).value =
    (keyM offset stride key).1 := rfl

theorem keyControl_peak : (keyControl (width := width) offset stride key).peak ≤ 7 := by rfl

def scalarControl (width value : Nat) : Control.Run (WordMachine.Word width) :=
  let result := (WordMachine.scalar width value).1
  Control.note result [.nat value,.ref result]

def mapControl (seed : β) (f : α → Control.Run β) (source : Vector α n) :=
  Control.tabulate seed (fun i : Fin n =>
    Control.scope [.ref source,.nat i.val] (Control.seq
      (Control.note source[i.val] [.ref source[i.val]]) f))

theorem mapControl_value (seed : β) (f : α → Control.Run β) (source : Vector α n) :
    (mapControl seed f source).value = source.map (fun x => (f x).value) := by
  simp only [mapControl,Control.tabulate_value,Control.scope,Control.seq,Control.note]
  apply Vector.ext
  intro i hi
  simp

theorem mapControl_peak (seed : β) (f : α → Control.Run β) (source : Vector α n)
    (hc : ∀ x, (f x).peak ≤ c) : (mapControl seed f source).peak ≤ c+11 := by
  have hh := Control.tabulate_peak seed
    (fun i : Fin n => Control.scope [.ref source,.nat i.val]
      (Control.seq (Control.note source[i.val] [.ref source[i.val]]) f))
    (c := c+3) (fun i => by
      simp only [Control.scope,Control.seq,Control.note,List.length_cons,List.length_nil]
      have hh := hc source[i.val]
      omega)
  exact hh

def rowControl (offset : Int) (stride : Nat) (source : Vector KeyBounds.Key n) :=
  mapControl (WordMachine.word width 0) (keyControl offset stride) source

theorem rowControl_value : (rowControl (width := width) offset stride source).value =
    (rowM offset stride source).1 := by
  simp only [rowControl,mapControl_value,keyControl_value,rowM,mapM_value]

theorem rowControl_peak : (rowControl (width := width) offset stride source).peak ≤ 18 :=
  mapControl_peak _ _ _ (fun _ => keyControl_peak)

def matrixControl (offset : Int) (stride : Nat) (source : Vector (Vector KeyBounds.Key cols) rows) :=
  Control.seq (Control.allocArray (WordMachine.word width 0) cols) fun seed =>
  Control.scope [.ref seed] (mapControl seed (rowControl offset stride) source)

theorem matrixControl_value : (matrixControl (width := width) offset stride source).value =
    (matrixM offset stride source).1 := by
  simp only [matrixControl,Control.seq,Control.scope,Control.allocArray,Control.note,
    mapControl_value,rowControl_value,matrixM,Resources.bind,TableExecution.initStore_exact,mapM_value]

theorem matrixControl_peak : (matrixControl (width := width) offset stride source).peak ≤ 30 := by
  have hh := mapControl_peak (Vector.replicate _ (WordMachine.word width 0))
    (rowControl offset stride) source (fun _ => rowControl_peak)
  simpa only [matrixControl,Control.seq,Control.scope,Control.allocArray,Control.note,
    List.length_cons,List.length_nil] using (max_le (show 4 ≤ 30 by omega) (show 1+_ ≤ 30 by omega))

def tensorControl (offset : Int) (stride : Nat)
    (source : Vector (Vector (Vector KeyBounds.Key cols) rows) classes) :=
  Control.seq (Control.allocArray (WordMachine.word width 0) cols) fun rowSeed =>
  Control.scope [.ref rowSeed] (Control.seq (Control.allocArray rowSeed rows) fun classSeed =>
    Control.scope [.ref classSeed] (mapControl classSeed (matrixControl offset stride) source))

theorem tensorControl_value : (tensorControl (width := width) offset stride source).value =
    (tensorM offset stride source).1 := by
  simp only [tensorControl,Control.seq,Control.scope,Control.allocArray,Control.note,
    mapControl_value,matrixControl_value,tensorM,Resources.bind,TableExecution.initStore_exact,mapM_value]

theorem tensorControl_peak : (tensorControl (width := width) offset stride source).peak ≤ 43 := by
  have hh := mapControl_peak (Vector.replicate _ (Vector.replicate _ (WordMachine.word width 0)))
    (matrixControl offset stride) source (fun _ => matrixControl_peak)
  simp only [tensorControl,Control.seq,Control.scope,Control.allocArray,Control.note,
    List.length_cons,List.length_nil]
  omega

def convertControl (data : Backend.State m) : Control.Run (Resident m width) :=
  Control.scope [.ref data] (
  Control.seq (mapControl (WordMachine.word width 0) (fun d : Int => scalarControl width d.toNat) data.micro.depths) fun depths =>
  Control.scope [.ref depths] (
  Control.seq (mapControl (WordMachine.word width 0) (fun c => scalarControl width c.val) data.micro.classes) fun classes =>
  Control.scope [.ref classes] (
  Control.seq (tensorControl ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1)) data.micro.shared) fun shared =>
  Control.scope [.ref shared] (
  Control.seq (Control.allocArray (WordMachine.word width 0) (blocks m)) fun seed =>
  Control.scope [.ref seed] (
  Control.seq (mapControl seed (fun desc => rowControl 0 (blocks m*(blockSize m-1+1)) desc.1) data.macroRows) fun macroRows =>
  Control.scope [.ref macroRows] (
  Control.seq (mapControl (WordMachine.word width 0) (fun desc => scalarControl width desc.2) data.macroRows) fun spans =>
  Control.scope [.ref spans] (
  Control.seq (mapControl (WordMachine.word width 0) (scalarControl width) data.macroLogs) fun logs =>
  Control.note ⟨depths,classes,shared,macroRows,spans,logs⟩ [.ref logs])))))))

theorem convertControl_value (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (data : Backend.State m) (valid : data = PackedBackend.state input) :
    (convertControl (width := width) data).value = (convertState input h data valid).1 := by
  simp only [convertControl,Control.scope,Control.seq,Control.note,mapControl_value,
    scalarControl,tensorControl_value,rowControl_value,Control.allocArray,
    convertState,Resources.bind,Resources.pure,TableExecution.initStore_exact,mapM_value]

theorem convertControl_peak (data : Backend.State m) :
    (convertControl (width := width) data).peak ≤ 128 := by
  have hd := mapControl_peak (WordMachine.word width 0) (fun d : Int => scalarControl width d.toNat)
    data.micro.depths (c := 2) (fun _ => le_rfl)
  have hc := mapControl_peak (WordMachine.word width 0) (fun c : Fin (2^(blockSize m-1)) => scalarControl width c.val)
    data.micro.classes (c := 2) (fun _ => le_rfl)
  have ht := tensorControl_peak (width := width) (offset := ((blockSize m-1 : Nat) : Int))
    (stride := 2*(blockSize m-1+1)) (source := data.micro.shared)
  have hm := mapControl_peak (Vector.replicate (blocks m) (WordMachine.word width 0))
    (fun desc : Vector KeyBounds.Key (blocks m) × Nat => rowControl 0 (blocks m*(blockSize m-1+1)) desc.1)
    data.macroRows (fun _ => rowControl_peak)
  have hs := mapControl_peak (WordMachine.word width 0)
    (fun desc : Vector KeyBounds.Key (blocks m) × Nat => scalarControl width desc.2)
    data.macroRows (c := 2) (fun _ => le_rfl)
  have hl := mapControl_peak (WordMachine.word width 0) (scalarControl width) data.macroLogs (c := 2) (fun _ => le_rfl)
  simp only [convertControl,Control.scope,Control.seq,Control.note,Control.allocArray,
    List.length_cons,List.length_nil]
  simp only [KeyBounds.Key, BlockedRMQ.Key] at hm hs ⊢
  omega



example : (repackM 4 (⟨9,by decide⟩ : WordMachine.Word 4)).1.val = 9 := by decide
example : (keyControl (width := 4) 2 4 (toLex (-1,1))).peak ≤ 7 := keyControl_peak

end Sequences.LCA.ResidentInstallation
