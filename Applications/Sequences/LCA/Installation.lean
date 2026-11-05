import Applications.Sequences.LCA.WordMachine

/-! Charged compaction from resident nested word buffers. Descriptor arithmetic
and payload reads execute before each destination write; tabulation counts
initialization, loop control and stores. -/
namespace Sequences.LCA.Installation
open Resources Dijkstra.Store
variable {width rows cols capacity base : Nat} [NeZero cols]

private def indexM (value bound : Nat) (hv : value < bound) (hw : value < 2^width) :
    Measured (Fin bound) Nat :=
  let run := WordMachine.scalar width value
  (⟨run.1.val,by change (WordMachine.word width value).val < bound; rw [WordMachine.word_of_lt hw]; exact hv⟩,run.2)

private theorem indexM_exact (value bound : Nat) (hv : value < bound) (hw : value < 2^width) :
    indexM (width := width) value bound hv hw = (⟨value,hv⟩,1) := by
  apply Prod.ext
  · apply Fin.ext; exact WordMachine.word_of_lt hw
  · rfl

def descriptorM (base rows cols i : Nat) : Measured (WordMachine.Word width) Nat :=
  bind (WordMachine.scalar width (i*cols)) fun product =>
  bind (WordMachine.scalar width (rows+product.val)) fun relative =>
  WordMachine.scalar width (base+relative.val)

theorem descriptorM_value (hh : base+rows+i*cols < 2^width) :
    (descriptorM (width := width) base rows cols i).1.val = base+rows+i*cols := by
  have hp : i*cols < 2^width := by omega
  have hr : rows+i*cols < 2^width := by omega
  simp [descriptorM,Resources.bind,WordMachine.scalar,WordMachine.word_of_lt hp,
    WordMachine.word_of_lt hr,WordMachine.word_of_lt (show base+(rows+i*cols)<2^width by omega),Nat.add_assoc]

theorem descriptorM_cost (base rows cols i : Nat) :
    (descriptorM (width := width) base rows cols i).2 = 3 := rfl

private theorem descriptorFits (fit : base+FlatTable.words rows cols ≤ capacity)
    (wide : capacity ≤ 2^width) (i : Fin rows) : base+rows+i.val*cols < 2^width := by
  have hp := NeZero.pos cols
  have hm := Nat.mul_le_mul_right cols (show i.val+1≤rows by omega)
  unfold FlatTable.words at fit
  nlinarith

def packCell (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (base capacity : Nat) (fit : base+FlatTable.words rows cols ≤ capacity)
    (wide : capacity ≤ 2^width) (i : Fin (FlatTable.words rows cols)) :
    Measured (WordMachine.Word width) Nat :=
  let run := if hi : i.val<rows then descriptorM base rows cols i.val else
    let pos := indexM (width := width) (i.val-rows) (rows*cols)
      (by have := i.isLt; unfold FlatTable.words at this; omega)
      (by have := i.isLt; omega)
    let row := indexM (width := width) (pos.1.val/cols) rows
      ((Nat.div_lt_iff_lt_mul (NeZero.pos cols)).2 pos.1.isLt)
      (by have := pos.1.isLt; have hd := Nat.div_le_self pos.1.val cols
          have hh := i.isLt; unfold FlatTable.words at hh fit; nlinarith)
    let col := indexM (width := width) (pos.1.val%cols) cols
      (Nat.mod_lt _ (NeZero.pos cols))
      (by have hm := Nat.mod_le pos.1.val cols; have := pos.1.isLt
          have hh := i.isLt; unfold FlatTable.words at hh fit; nlinarith)
    let resident := TableExecution.read cells row.1
    let word := TableExecution.read resident.1 col.1
    (word.1,pos.2+row.2+col.2+resident.2+word.2)
  (run.1,1+run.2)

theorem packCell_cost (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin (FlatTable.words rows cols)) : (packCell cells base capacity fit wide i).2 ≤ 6 := by
  unfold packCell
  split <;> simp [descriptorM_cost,indexM,TableExecution.read]

theorem packCell_value (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin (FlatTable.words rows cols)) :
    (packCell cells base capacity fit wide i).1 = (FlatTable.pack cells base capacity fit wide)[i.val] := by
  by_cases hi : i.val<rows
  · apply Fin.ext
    simp only [packCell,hi,dite_true]
    rw [descriptorM_value (descriptorFits fit wide ⟨i.val,hi⟩)]
    exact (FlatTable.descriptor_read cells fit wide ⟨i.val,hi⟩).symm
  · have hp : i.val-rows < rows*cols := by have := i.isLt; unfold FlatTable.words at this; omega
    let r : Fin rows := ⟨(i.val-rows)/cols,(Nat.div_lt_iff_lt_mul (NeZero.pos cols)).2 hp⟩
    let c : Fin cols := ⟨(i.val-rows)%cols,Nat.mod_lt _ (NeZero.pos cols)⟩
    have he : rows+r.val*cols+c.val=i.val := by
      have hh : (i.val-rows)/cols*cols+(i.val-rows)%cols=i.val-rows := by simpa [Nat.mul_comm] using Nat.div_add_mod (i.val-rows) cols
      dsimp [r,c]
      omega
    have hh := FlatTable.payload_read cells fit wide r c
    have hz : (packCell cells base capacity fit wide i).1 = cells[r.val][c.val] := by
      simp only [packCell,hi,dite_false,indexM_exact,TableExecution.read,lookup]
      rfl
    rw [hz]
    simpa only [he] using hh.symm

def packM (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (base capacity : Nat) (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :=
  TableExecution.tabulate (WordMachine.word width 0) (packCell cells base capacity fit wide)

theorem packM_value (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :
    (packM cells base capacity fit wide).1 = FlatTable.pack cells base capacity fit wide := by
  rw [packM,TableExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simpa only [Vector.getElem_ofFn] using packCell_value cells fit wide ⟨i,hi⟩

theorem packM_cost (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :
    (packM cells base capacity fit wide).2 ≤ 12*FlatTable.words rows cols := by
  simpa [packM,Nat.mul_comm] using TableExecution.tabulate_cost (WordMachine.word width 0)
    (packCell cells base capacity fit wide) 6 (packCell_cost cells fit wide)

theorem packM_slots (cells : Vector (Vector (WordMachine.Word width) cols) rows)
    (fit : base+FlatTable.words rows cols ≤ capacity) (wide : capacity ≤ 2^width) :
    (packM cells base capacity fit wide).1.toArray.size = FlatTable.words rows cols := Vector.size_toArray _

variable {classes : Nat} [NeZero rows]

private instance innerWords_neZero : NeZero (FlatTable.words rows cols) := by
  constructor
  have hr := NeZero.pos rows
  unfold FlatTable.words
  omega

theorem inner_fit (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (code : Fin classes) :
    base+classes+code.val*FlatTable.words rows cols+FlatTable.words rows cols ≤ capacity := by
  have hm := Nat.mul_le_mul_right (FlatTable.words rows cols) (show code.val+1≤classes by omega)
  change base+(classes+classes*FlatTable.words rows cols) ≤ capacity at fit
  nlinarith

def tensorPack (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (base capacity : Nat) (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :=
  FlatTable.pack (Vector.ofFn fun code : Fin classes =>
    FlatTable.pack cells[code.val] (base+classes+code.val*FlatTable.words rows cols) capacity (inner_fit fit code) wide)
    base capacity fit wide

def tensorClassM (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (base capacity : Nat) (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :=
  let pointer := descriptorM (width := width) base classes (FlatTable.words rows cols) code.val
  let resident := TableExecution.read cells code
  let packed := packM resident.1 pointer.1.val capacity (by
    rw [descriptorM_value (descriptorFits fit wide code)]
    exact inner_fit fit code) wide
  (packed.1,pointer.2+resident.2+packed.2)

theorem tensorClassM_value (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :
    (tensorClassM cells base capacity fit wide code).1 =
      FlatTable.pack cells[code.val] (base+classes+code.val*FlatTable.words rows cols) capacity (inner_fit fit code) wide := by
  simp only [tensorClassM,packM_value,TableExecution.read,lookup,
    descriptorM_value (descriptorFits fit wide code)]

theorem tensorClassM_cost (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) (code : Fin classes) :
    (tensorClassM cells base capacity fit wide code).2 ≤ 12*FlatTable.words rows cols+4 := by
  unfold tensorClassM
  have hh := packM_cost (TableExecution.read cells code).1
    (show (descriptorM (width := width) base classes (FlatTable.words rows cols) code.val).1.val+
      FlatTable.words rows cols ≤ capacity by
      rw [descriptorM_value (descriptorFits fit wide code)]; exact inner_fit fit code) wide
  simp only [descriptorM_cost,TableExecution.read] at hh ⊢
  omega

def tensorM (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (base capacity : Nat) (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :=
  bind (TableExecution.initStore (WordMachine.word width 0) (FlatTable.words rows cols)) fun seedClass =>
  bind (TableExecution.tabulate seedClass (tensorClassM cells base capacity fit wide)) fun compactClasses =>
  packM compactClasses base capacity fit wide

theorem tensorM_value (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    (tensorM cells base capacity fit wide).1 = tensorPack cells base capacity fit wide := by
  simp only [tensorM,Resources.bind,packM_value,TableExecution.tabulate_value,tensorClassM_value,tensorPack]

theorem tensorM_cost (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    (tensorM cells base capacity fit wide).2 ≤
      3*FlatTable.words rows cols+classes*(12*FlatTable.words rows cols+10)+
        12*FlatTable.words classes (FlatTable.words rows cols) := by
  have ht := TableExecution.tabulate_cost
    (TableExecution.initStore (WordMachine.word width 0) (FlatTable.words rows cols)).1
    (tensorClassM cells base capacity fit wide) (12*FlatTable.words rows cols+4)
    (tensorClassM_cost cells fit wide)
  have hp := packM_cost
    (TableExecution.tabulate
      (TableExecution.initStore (WordMachine.word width 0) (FlatTable.words rows cols)).1
      (tensorClassM cells base capacity fit wide)).1 fit wide
  simp only [tensorM,Resources.bind,TableExecution.initStore_exact]
  simp only [TableExecution.initStore_exact] at ht hp
  have hc : 12*FlatTable.words rows cols+4+6=12*FlatTable.words rows cols+10 := by omega
  rw [hc] at ht
  omega

/-- This is the live allocation budget for the stated copying schedule: one
seed class, the intermediate compact classes and their pointer vector, then
the final descriptor/payload output. Resident input buffers are additional. -/
def tensorAllocation (classes rows cols : Nat) :=
  FlatTable.words rows cols + classes*(FlatTable.words rows cols+1)+
    FlatTable.words classes (FlatTable.words rows cols)

/-- Observe every constructed buffer in the actual compaction schedule.
The class seed is shared by pointer initialization rather than deep-copied. -/
def tensorSlotsObserved
    (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (base capacity : Nat) (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) : Nat :=
  let seed := (TableExecution.initStore (WordMachine.word width 0) (FlatTable.words rows cols)).1
  let intermediates := (TableExecution.tabulate seed (tensorClassM cells base capacity fit wide)).1
  let output := (packM intermediates base capacity fit wide).1
  seed.toArray.size + intermediates.toArray.size +
    (∑ i : Fin classes, (intermediates[i.val]).toArray.size) + output.toArray.size

theorem tensorSlotsObserved_eq
    (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    tensorSlotsObserved cells base capacity fit wide = tensorAllocation classes rows cols := by
  simp [tensorSlotsObserved,Vector.size_toArray,tensorAllocation]
  ring

theorem tensorM_slots (cells : Vector (Vector (Vector (WordMachine.Word width) cols) rows) classes)
    (fit : base+FlatTable.words classes (FlatTable.words rows cols) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    (tensorM cells base capacity fit wide).1.toArray.size =
      FlatTable.words classes (FlatTable.words rows cols) := Vector.size_toArray _

/-- Compact the already resident shared table; the input tensor is read by
`tensorM`, not recomputed from its semantic class code. -/
def sharedM (steps : Nat)
    (cells : Vector (Vector (Vector (WordMachine.Word width) (steps+1)) (steps+1)) (2^steps))
    (base capacity : Nat)
    (fit : base+FlatTable.words (2^steps) (FlatTable.words (steps+1) (steps+1)) ≤ capacity)
    (wide : capacity ≤ 2^width) := tensorM cells base capacity fit wide

theorem sharedM_value (steps : Nat)
    (cells : Vector (Vector (Vector (WordMachine.Word width) (steps+1)) (steps+1)) (2^steps))
    (keyWidth : (2*steps+1)*(2*(steps+1)) ≤ 2^width)
    (hc : ∀ code : Fin (2^steps), cells[code.val] = FlatTable.microMatrix code keyWidth)
    (fit : base+FlatTable.words (2^steps) (FlatTable.words (steps+1) (steps+1)) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    (sharedM steps cells base capacity fit wide).1 = FlatTable.sharedPack steps base capacity keyWidth fit wide := by
  rw [sharedM,tensorM_value]
  have he : cells = Vector.ofFn (fun code : Fin (2^steps) => FlatTable.microMatrix code keyWidth) := by
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_ofFn] using hc ⟨i,hi⟩
  rw [he]
  simp only [tensorPack,FlatTable.sharedPack,FlatTable.sharedCells,Vector.getElem_ofFn]

theorem sharedM_cost (steps : Nat)
    (cells : Vector (Vector (Vector (WordMachine.Word width) (steps+1)) (steps+1)) (2^steps))
    (fit : base+FlatTable.words (2^steps) (FlatTable.words (steps+1) (steps+1)) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    (sharedM steps cells base capacity fit wide).2 ≤
      3*FlatTable.words (steps+1) (steps+1)+
      2^steps*(12*FlatTable.words (steps+1) (steps+1)+10)+
      12*FlatTable.words (2^steps) (FlatTable.words (steps+1) (steps+1)) :=
  tensorM_cost cells fit wide

private def sample : Vector (Vector (WordMachine.Word 8) 2) 2 :=
  #v[#v[⟨9,by decide⟩,⟨8,by decide⟩],#v[⟨7,by decide⟩,⟨6,by decide⟩]]

example : ((packM sample 10 32 (by decide) (by decide)).1[0]).val = 12 := by decide
example : ((packM sample 10 32 (by decide) (by decide)).1[1]).val = 14 := by decide
example : ((packM sample 10 32 (by decide) (by decide)).1[4]).val = 7 := by decide
example : (packM sample 10 32 (by decide) (by decide)).2 ≤ 72 := packM_cost sample (by decide) (by decide)

end Sequences.LCA.Installation
