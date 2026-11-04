import Applications.Sequences.LCA.PackedBackend

/-! Reads from the installed whole arena at the global payload addresses. -/
namespace Sequences.LCA.PackedReads
open PreparationBounds PackedBackend TreeReduction Dijkstra.Store
variable {m width capacity inputWords frameWords : Nat}

def sharedAddress (i : Fin (FlatTable.words (2^(blockSize m-1))
    (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)))) : Fin (retainedSlots m) :=
  ⟨paddedCapacity m+blocks m+i.val, by
    have hi := i.isLt
    have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
      rw [FlatTable.sharedPack_size,dimension]; rfl
    have hi2 := lt_of_lt_of_eq hi hs
    unfold retainedSlots SparseExecution.retainedSlots
    omega⟩

def macroAddress (i : Fin (FlatTable.words (levels m+1) (blocks m))) : Fin (retainedSlots m) :=
  ⟨macroBase m+i.val, by
    have hi := i.isLt
    unfold macroBase retainedSlots SparseExecution.retainedSlots FlatTable.words at *
    nlinarith⟩

theorem flatten_shared (r : Representation m width)
    (i : Fin (FlatTable.words (2^(blockSize m-1))
      (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)))) :
    r.flatten[(sharedAddress i).val] = r.shared[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,sharedAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  split_ifs <;> try omega
  congr 1
  omega

theorem flatten_macro (r : Representation m width)
    (i : Fin (FlatTable.words (levels m+1) (blocks m))) :
    r.flatten[(macroAddress i).val] = r.macroTable[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,macroAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
    rw [FlatTable.sharedPack_size,dimension]; rfl
  unfold macroBase
  split_ifs <;> try omega
  congr 1
  omega

theorem arena_shared (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (FlatTable.words (2^(blockSize m-1))
      (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)))) :
    lookup (arena input h) ⟨(sharedAddress i).val, by
      have hh := h.memory; have hi := (sharedAddress i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩ = (sharedWords input h)[i.val] := by
  rw [arena_read input h (sharedAddress i),flatten_shared]
  rfl

theorem arena_macro (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (FlatTable.words (levels m+1) (blocks m))) :
    lookup (arena input h) ⟨(macroAddress i).val, by
      have hh := h.memory; have hi := (macroAddress i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩ = (macroPack input h)[i.val] := by
  rw [arena_read input h (macroAddress i),flatten_macro]
  rfl

def sharedPayload (code : Fin (2^(blockSize m-1)))
    (start len : Fin (blockSize m-1+1)) :=
  sharedAddress (⟨2^(blockSize m-1)+
    code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
    ((blockSize m-1+1)+start.val*(blockSize m-1+1)+len.val),
    FlatTable.payload_index_lt code ⟨_,FlatTable.payload_index_lt start len⟩⟩)

def macroPayload (level : Fin (levels m+1)) (i : Fin (blocks m)) :=
  macroAddress ⟨(levels m+1)+level.val*blocks m+i.val,FlatTable.payload_index_lt level i⟩

theorem arena_shared_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    (lookup (arena input h) ⟨(sharedPayload code start len).val, by
      have hh := h.memory; have hi := (sharedPayload code start len).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val =
      WordKey.encode ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1))
        (ofLex ((((state input).micro.shared.get code).get start).get len)).1
        (ofLex ((((state input).micro.shared.get code).get start).get len)).2 := by
  simp only [sharedPayload]
  rw [arena_shared]
  exact sharedWords_read input h code start len

theorem arena_macro_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (lookup (arena input h) ⟨(macroPayload level i).val, by
      have hh := h.memory; have hi := (macroPayload level i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val =
      WordKey.encode 0 (blocks m*(blockSize m-1+1))
        (ofLex ((state input).macroRows[level.val]).1[i.val]).1
        (ofLex ((state input).macroRows[level.val]).1[i.val]).2 := by
  simp only [macroPayload]
  rw [arena_macro]
  exact macroPack_read input h level i

def macroDescriptor (level : Fin (levels m+1)) :=
  macroAddress (⟨level.val,by have := level.isLt; unfold FlatTable.words; omega⟩ :
    Fin (FlatTable.words (levels m+1) (blocks m)))

theorem arena_macro_descriptor (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) :
    (lookup (arena input h) ⟨(macroDescriptor level).val, by
      have hh := h.memory; have hi := (macroDescriptor level).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val =
      macroBase m+(levels m+1)+level.val*blocks m := by
  simp only [macroDescriptor]
  rw [arena_macro]
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  exact FlatTable.descriptor_read (macroWords input h.toWordEligible) (macro_fit h) h.addresses level

/-- The descriptor read from the installed arena points to the first payload
word of the selected row, so adding the column yields its actual global address. -/
theorem macro_payload_from_descriptor (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (macroPayload level i).val = macroBase m+(levels m+1)+level.val*blocks m+i.val := by
  simp only [macroPayload,macroAddress]
  omega

/-- Singleton layout checks include both levels of shared descriptors and
the reserved block-minimum slot before the macro descriptor. -/
example : (sharedPayload (m := 1) ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩).val = 4 := by decide
example : (macroDescriptor (m := 1) ⟨0,by decide⟩).val = 6 := by decide
example : (macroPayload (m := 1) ⟨0,by decide⟩ ⟨0,by decide⟩).val = 7 := by decide

end Sequences.LCA.PackedReads
