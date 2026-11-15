import Applications.Sequences.LCA.WordWithin
import Applications.Sequences.LCA.PreparationCertificate

namespace Sequences.LCA.PreparationMinima
open Resources Dijkstra.Store PreparationBounds PackedBackend WordMachine
variable {m width capacity inputWords frameWords : Nat}

def prefixSize (m : Nat) := paddedCapacity m + blocks m + sharedSlots m

def PrefixAgrees (left right : Store capacity (Word width)) : Prop :=
  ∀ i : Fin capacity, i.val < prefixSize m → lookup left i = lookup right i

/-- A proof-state witness with the micro prefix retained and all later cells
zero. This is not an additional runtime construction pass. -/
def microMemory (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : Store capacity (Word width) :=
  Vector.ofFn fun i => if i.val < prefixSize m then lookup (arena input h) i else word width 0

theorem microMemory_agrees (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    PrefixAgrees (m := m) (microMemory input h) (arena input h) := by
  intro i hi
  simp [microMemory,lookup,hi]

theorem microMemory_suffix (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin capacity) (hi : prefixSize m ≤ i.val) :
    lookup (microMemory input h) i = word width 0 := by
  simp [microMemory,lookup,show ¬ i.val < prefixSize m by omega]

theorem load_prefix {left right : Store capacity (Word width)}
    (he : PrefixAgrees (m := m) left right) (base index : Nat)
    (hi : base+index < prefixSize m) : load left base index = load right base index := by
  unfold load
  split
  · rw [he _ hi]
  · rfl

theorem shared_size :
    FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
  rw [FlatTable.sharedPack_size,dimension]
  rfl

theorem shared_index_lt (i : Fin (FlatTable.words (2^(blockSize m-1))
    (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)))) :
    paddedCapacity m+blocks m+i.val < prefixSize m := by
  have hi : i.val < sharedSlots m := by simpa only [shared_size] using i.isLt
  unfold prefixSize
  omega

theorem prefix_reads (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (mem : Store capacity (Word width))
    (he : PrefixAgrees (m := m) mem (arena input h)) : WordWithin.MicroReads input mem where
  load_class i := by
    rw [load_prefix he _ _ (by have := i.isLt; unfold prefixSize; omega)]
    exact WordLoads.load_class input h i
  load_sharedDescriptor code := by
    have hh := shared_index_lt (m := m) (⟨code.val,by
      have := code.isLt; unfold FlatTable.words; omega⟩ : Fin _)
    rw [load_prefix he _ _ hh]
    exact WordLoads.load_sharedDescriptor input h code
  load_sharedRowDescriptor code start := by
    have hh := shared_index_lt (m := m) (⟨_,FlatTable.payload_index_lt code
      (⟨start.val,by have := start.isLt; unfold FlatTable.words; omega⟩ : Fin _)⟩ : Fin _)
    rw [load_prefix he _ _ (by simpa only [Fin.val_mk,Nat.add_assoc] using hh)]
    exact WordLoads.load_sharedRowDescriptor input h code start
  load_sharedPayload code start len := by
    have hh := shared_index_lt (m := m) (⟨_,FlatTable.payload_index_lt code
      (⟨_,FlatTable.payload_index_lt start len⟩ : Fin _)⟩ : Fin _)
    rw [load_prefix he _ _ (by simpa only [Fin.val_mk,Nat.add_assoc] using hh)]
    exact WordLoads.load_sharedPayload input h code start len
  load_depth i := by
    rw [load_prefix he _ _ (by
      have hi : i.val < paddedCapacity m := by simpa only [dimension,paddedCapacity] using i.isLt
      unfold prefixSize
      omega)]
    exact WordLoads.load_depth input h i

def minima (m : Nat) (mem : Store capacity (Word width)) :=
  TableExecution.tabulate (word width 0) (fun block : Fin (blocks m) =>
    WordWithin.within m mem block.val 0 (blockSize m-1))

def encodeKey (m : Nat) (key : BlockedRMQ.Key) :=
  WordKey.encode 0 (paddedCapacity m) (ofLex key).1 (ofLex key).2

theorem minima_value (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (mem : Store capacity (Word width))
    (he : PrefixAgrees (m := m) mem (arena input h)) :
    (minima m mem).1.map Fin.val =
      ((Preparation.minimaM (state input).micro (blocks_pos m)).1.map (encodeKey m)) := by
  simp only [minima,TableExecution.tabulate_value,Preparation.minimaM_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map,Vector.getElem_ofFn,BlockedRMQ.blockMinima]
  exact WordWithin.within_value_of_reads input h mem (prefix_reads input h mem he)
    hi (by have := blockSize_pos m; omega)

theorem minima_refines (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (mem : Store capacity (Word width))
    (he : PrefixAgrees (m := m) mem (arena input h)) :
    TableTransport.transport (Vector.map Fin.val) (minima m mem) =
      TableTransport.transport (Vector.map (encodeKey m))
        (Preparation.minimaM (state input).micro (blocks_pos m)) := by
  unfold minima Preparation.minimaM
  rw [← TableTransport.tabulate_transport,← TableTransport.tabulate_transport]
  have seed : (word width 0).val = encodeKey m (toLex ((0 : Int),(0 : Nat))) := by
    simp [word,encodeKey,WordKey.encode,WordKey.pack]
  rw [seed]
  congr 1
  funext block
  apply Prod.ext
  · change (WordWithin.within m mem block.val 0 (blockSize m-1)).1.val = _
    simp only [TableTransport.transport,BlockedRMQ.withinMeasured_value]
    exact WordWithin.within_value_of_reads input h mem (prefix_reads input h mem he)
      block.isLt (by have := blockSize_pos m; omega)
  · simp only [TableTransport.transport,WordWithin.within_cost,BlockedRMQ.withinMeasured_cost]

theorem minima_cost (m : Nat) (mem : Store capacity (Word width)) :
    (minima m mem).2 ≤ 20*blocks m := by
  have hh := TableExecution.tabulate_cost (word width 0)
    (fun block : Fin (blocks m) => WordWithin.within m mem block.val 0 (blockSize m-1)) 14
    (fun _ => (WordWithin.within_cost _ _ _ _ _).le)
  simpa only [minima,Nat.mul_comm] using hh

open PreparationCertificate

theorem minima_wide_input (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (mem : Store capacity (Word width))
    (he : PrefixAgrees (m := m) mem (arena input h)) :
    (minima m mem).1 =
      (WordKey.encodeStore (liftVector
        (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (macroMinima_fits input))).map
        (widen ((KeyBounds.macro_capacity_le (paddedCapacity_le input.positive)).trans h.keys)) := by
  have hh := minima_value input h mem he
  apply Vector.ext
  intro i hi
  apply Fin.ext
  have hh' := congrArg (fun v => v[i]) hh
  simp only [Vector.getElem_map,Preparation.minimaM_value] at hh'
  simpa only [Vector.getElem_map,WordKey.encodeStore,liftVector,Vector.getElem_ofFn,
    widen,WordKey.cellWord,encodeKey,WordKey.encode] using hh'

/-- The actually computed finite-word minima feed the actual sparse builder.
No semantic minima vector is substituted at execution time. -/
def finish (m : Nat) (mem : Store capacity (Word width)) :=
  bind (minima m mem) fun values => SparseExecution.prepare (word width 0) values (levels m)

theorem finish_eq (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (mem : Store capacity (Word width))
    (he : PrefixAgrees (m := m) mem (arena input h)) :
    finish m mem = ((wideMacroProgram input h.toWordEligible).1,
      (Preparation.minimaM (state input).micro (blocks_pos m)).2+
        (wideMacroProgram input h.toWordEligible).2) := by
  have hc := congrArg Prod.snd (minima_refines input h mem he)
  change (minima m mem).2 = (Preparation.minimaM (state input).micro (blocks_pos m)).2 at hc
  unfold finish
  simp only [Resources.bind,minima_wide_input input h mem he,hc]
  have hs : word width 0 = widen
      ((KeyBounds.macro_capacity_le (paddedCapacity_le input.positive)).trans h.keys)
      (WordKey.cellWord (macroSeed input)) := by
    apply Fin.ext
    simp [word,widen,WordKey.cellWord,macroSeed,WordKey.encode,WordKey.pack]
  rw [hs]
  rfl

theorem finish_payload (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (mem : Store capacity (Word width))
    (he : PrefixAgrees (m := m) mem (arena input h))
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (((finish m mem).1.1[level.val]).1[i.val]) =
      ((macroPack input h)[(levels m+1)+level.val*blocks m+i.val]'
        (FlatTable.payload_index_lt level i)) := by
  rw [finish_eq input h mem he,wideMacroProgram_refines]
  simp only [TableTransport.transport,TableTransport.rowsMap,Vector.getElem_map]
  exact macroProgram_physical input h level i

theorem finish_cost (m : Nat) (mem : Store capacity (Word width)) :
    (finish m mem).2 ≤ 34*blocks m+3+levels m*(11*blocks m+7) := by
  have hm := minima_cost m mem
  have hs := SparseExecution.prepare_cost (word width 0) (minima m mem).1 (levels m)
  simp only [finish,Resources.bind]
  omega

-- The suffix is zero even while the macro tables are not yet constructed.
example (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (minima m (microMemory input h)).1.map Fin.val =
      (Preparation.minimaM (state input).micro (blocks_pos m)).1.map (encodeKey m) :=
  minima_value input h _ (microMemory_agrees input h)

example (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (finish m (microMemory input h)).1 = (wideMacroProgram input h.toWordEligible).1 := by
  rw [finish_eq input h _ (microMemory_agrees input h)]

end Sequences.LCA.PreparationMinima
