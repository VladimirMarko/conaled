import Applications.Sequences.LCA.ResidentInstallation

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.PackingControl
open PreparationBounds PackedBackend ResidentInstallation Control
variable {width rows cols classes base capacity : Nat} [NeZero cols] [NeZero rows]

private instance inner_nonzero : NeZero (FlatTable.words rows cols) := by
  constructor
  have hh := NeZero.pos rows
  unfold FlatTable.words
  omega

private theorem descriptor_bound
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :
    base+classes+code.val*FlatTable.words rows cols < 2^width := by
  have hh := Installation.inner_fit fit code
  have hp := NeZero.pos (FlatTable.words rows cols)
  omega

/-- The class call retains its source reference, layout arguments, executed
pointer arithmetic, and selected resident matrix across the inner pack loop. -/
def classRun (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :=
  let product := (WordMachine.scalar width (code.val*FlatTable.words rows cols)).1
  let relative := (WordMachine.scalar width (classes+product.val)).1
  let pointer := (Installation.descriptorM (width := width) base classes (FlatTable.words rows cols) code.val).1
  let resident := (TableExecution.read cells code).1
  scope [.ref cells,.nat base,.nat capacity,.nat classes,.nat rows,.nat cols,
    .nat code.val,.ref product,.ref relative,.ref pointer,.ref resident]
    (packControl resident (show pointer.val+FlatTable.words rows cols ≤ capacity by
      dsimp only [pointer]
      rw [Installation.descriptorM_value (descriptor_bound fit wide code)]
      exact Installation.inner_fit fit code) wide)

theorem classRun_value (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :
    (classRun cells fit wide code).value = (Installation.tensorClassM cells base capacity fit wide code).1 := by
  simp only [classRun,scope,packControl_value,Installation.tensorClassM]

theorem classRun_peak (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :
    (classRun cells fit wide code).peak ≤ 31 := by
  unfold classRun
  have hh := packControl_peak (TableExecution.read cells code).1
    (show (Installation.descriptorM (width := width) base classes (FlatTable.words rows cols) code.val).1.val+
      FlatTable.words rows cols ≤ capacity by
      rw [Installation.descriptorM_value (descriptor_bound fit wide code)]
      exact Installation.inner_fit fit code) wide
  simp only [scope,List.length_cons,List.length_nil]
  omega

/-- Follow the initialized seed, class tabulation, then outer relocation.
References saved across a call occupy one scalar slot; payload buffers are
counted separately by `Installation.tensorSlotsObserved`. -/
def tensorRun (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :=
  scope [.ref cells,.nat base,.nat capacity,.nat classes,.nat rows,.nat cols]
    (seq (allocArray (WordMachine.word width 0) (FlatTable.words rows cols)) fun seed =>
      scope [.ref seed] (seq (tabulate seed (classRun cells fit wide)) fun compact =>
        scope [.ref compact] (packControl compact fit wide)))

theorem tensorRun_value (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    (tensorRun cells fit wide).value = (Installation.tensorM cells base capacity fit wide).1 := by
  simp only [tensorRun,scope,seq,tabulate_value,classRun_value,packControl_value,
    Installation.tensorM,Resources.bind,TableExecution.initStore_exact,TableExecution.tabulate_value,
    allocArray,note]

theorem tensorRun_peak (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) : (tensorRun cells fit wide).peak ≤ 64 := by
  have ht := tabulate_peak (allocArray (WordMachine.word width 0) (FlatTable.words rows cols)).value
    (classRun cells fit wide) (classRun_peak cells fit wide)
  have hp := packControl_peak
    (tabulate (allocArray (WordMachine.word width 0) (FlatTable.words rows cols)).value
      (classRun cells fit wide)).value fit wide
  simp only [tensorRun,scope,seq,allocArray,note,List.length_cons,List.length_nil] at ht hp ⊢
  omega

variable {m inputWords frameWords : Nat}

/-- Retain the resident record and completed shared output while relocating
macro rows. The final constructor observes all six output fields. -/
def packRun (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : Run (Representation m width) :=
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  scope [.ref r] (seq (tensorRun r.shared (sharedFits h) h.addresses) fun shared =>
    scope [.ref shared] (seq (packControl r.macroRows (macro_fit h) h.addresses) fun packedMacro =>
      note ⟨r.depths,r.classes,shared,packedMacro,r.spans,r.logs⟩
        [.ref r.depths,.ref r.classes,.ref shared,.ref packedMacro,.ref r.spans,.ref r.logs]))

theorem packRun_value (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (packRun r h).value = (packResident r h).1 := by
  simp only [packRun,scope,seq,note,tensorRun_value,packControl_value,
    packResident,Resources.bind,Resources.pure,Installation.sharedM]

theorem packRun_peak (r : Resident m width)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (packRun r h).peak ≤ 128 := by
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  have hs := tensorRun_peak r.shared (sharedFits h) h.addresses
  have hm := packControl_peak r.macroRows (macro_fit h) h.addresses
  simp only [packRun,scope,seq,note,List.length_cons,List.length_nil]
  omega

private def sample : Vector (Vector (Vector (WordMachine.Word 8) 2) 2) 1 :=
  #v[#v[#v[WordMachine.word 8 9,WordMachine.word 8 8],
    #v[WordMachine.word 8 7,WordMachine.word 8 6]]]

-- The nested resident packing executes with 38 simultaneous control slots.
example : (tensorRun sample (show 10+FlatTable.words 1 (FlatTable.words 2 2)≤64 by decide)
    (by decide)).peak = 38 := by decide

end Sequences.LCA.PackingControl
