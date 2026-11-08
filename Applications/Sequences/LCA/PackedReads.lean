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
  all_goals first | rfl | (congr 1; omega)

theorem flatten_macro (r : Representation m width)
    (i : Fin (FlatTable.words (levels m+1) (blocks m))) :
    r.flatten[(macroAddress i).val] = r.macroTable[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,macroAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
    rw [FlatTable.sharedPack_size,dimension]; rfl
  try unfold macroBase
  split_ifs <;> try omega
  all_goals first | rfl | (congr 1; omega)

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

def depthAddress (i : Fin (blocks m*(blockSize m-1+1))) : Fin (retainedSlots m) :=
  ⟨i.val, by
    have hi := i.isLt
    have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
    simp only [macroBase,retainedSlots,SparseExecution.retainedSlots,FlatTable.words]
    nlinarith⟩

theorem flatten_depth (r : Representation m width) (i : Fin (blocks m*(blockSize m-1+1))) :
    r.flatten[(depthAddress i).val] = r.depths[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,depthAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
    rw [FlatTable.sharedPack_size,dimension]; rfl
  try unfold macroBase
  split_ifs <;> try omega
  all_goals first | rfl | (congr 1; omega)

theorem arena_depth_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (blocks m*(blockSize m-1+1))) :
    ((lookup (arena input h) ⟨(depthAddress i).val, by
      have hh := h.memory; have hi := (depthAddress i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val : Int) = (state input).micro.depths[i.val] := by
  rw [arena_read input h (depthAddress i),flatten_depth]
  exact depthWords_read input h.toWordEligible i

def classAddress (i : Fin (blocks m)) : Fin (retainedSlots m) :=
  ⟨paddedCapacity m+i.val, by
    have hi := i.isLt
    have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
    simp only [macroBase,retainedSlots,SparseExecution.retainedSlots,FlatTable.words]
    nlinarith⟩

theorem flatten_class (r : Representation m width) (i : Fin (blocks m)) :
    r.flatten[(classAddress i).val] = r.classes[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,classAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
    rw [FlatTable.sharedPack_size,dimension]; rfl
  try unfold macroBase
  split_ifs <;> try omega
  all_goals first | rfl | (congr 1; omega)

theorem arena_class_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (blocks m)) :
    (lookup (arena input h) ⟨(classAddress i).val, by
      have hh := h.memory; have hi := (classAddress i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val = ((state input).micro.classes[i.val]).val := by
  rw [arena_read input h (classAddress i),flatten_class]
  exact classWords_read input h.toWordEligible i

def spanAddress (i : Fin (levels m+1)) : Fin (retainedSlots m) :=
  ⟨macroBase m+FlatTable.words (levels m+1) (blocks m)+i.val, by
    have hi := i.isLt
    have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
    simp only [macroBase,retainedSlots,SparseExecution.retainedSlots,FlatTable.words]
    nlinarith⟩

theorem flatten_span (r : Representation m width) (i : Fin (levels m+1)) :
    r.flatten[(spanAddress i).val] = r.spans[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,spanAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
    rw [FlatTable.sharedPack_size,dimension]; rfl
  try unfold macroBase
  split_ifs <;> try omega
  all_goals first | rfl | (congr 1; omega)

theorem arena_span_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (levels m+1)) :
    (lookup (arena input h) ⟨(spanAddress i).val, by
      have hh := h.memory; have hi := (spanAddress i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val = ((state input).macroRows[i.val]).2 := by
  rw [arena_read input h (spanAddress i),flatten_span]
  exact spanWords_read input h.toWordEligible i

def logAddress (i : Fin (blocks m+1)) : Fin (retainedSlots m) :=
  ⟨macroBase m+FlatTable.words (levels m+1) (blocks m)+(levels m+1)+i.val, by
    have hi := i.isLt
    have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
    simp only [macroBase,retainedSlots,SparseExecution.retainedSlots,FlatTable.words]
    nlinarith⟩

theorem flatten_log (r : Representation m width) (i : Fin (blocks m+1)) :
    r.flatten[(logAddress i).val] = r.logs[i.val] := by
  have hi := i.isLt
  simp only [Representation.flatten,logAddress,Vector.getElem_cast,Vector.getElem_append]
  have hd : blocks m*(blockSize m-1+1) = paddedCapacity m := by rw [dimension]; rfl
  have hs : FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) = sharedSlots m := by
    rw [FlatTable.sharedPack_size,dimension]; rfl
  try unfold macroBase
  split_ifs <;> try omega
  all_goals first | rfl | (congr 1; omega)

theorem arena_log_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (blocks m+1)) :
    (lookup (arena input h) ⟨(logAddress i).val, by
      have hh := h.memory; have hi := (logAddress i).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val = (state input).macroLogs[i.val] := by
  rw [arena_read input h (logAddress i),flatten_log]
  exact logWords_read input h.toWordEligible i

def sharedDescriptor (code : Fin (2^(blockSize m-1))) :=
  sharedAddress (⟨code.val,by have := code.isLt; unfold FlatTable.words; omega⟩ :
    Fin (FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1))))

def sharedRowDescriptor (code : Fin (2^(blockSize m-1))) (start : Fin (blockSize m-1+1)) :=
  sharedAddress (⟨2^(blockSize m-1)+code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+start.val,
    FlatTable.payload_index_lt code ⟨start.val,by have := start.isLt; unfold FlatTable.words; omega⟩⟩)

theorem arena_shared_descriptor (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) :
    (lookup (arena input h) ⟨(sharedDescriptor code).val, by
      have hh := h.memory; have hi := (sharedDescriptor code).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val =
      paddedCapacity m+blocks m+2^(blockSize m-1)+
        code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1) := by
  simp only [sharedDescriptor]
  rw [arena_shared]
  let : NeZero (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) := ⟨by unfold FlatTable.words; omega⟩
  unfold sharedWords FlatTable.sharedPack
  exact FlatTable.descriptor_read _ _ _ code

theorem arena_shared_row_descriptor (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start : Fin (blockSize m-1+1)) :
    (lookup (arena input h) ⟨(sharedRowDescriptor code start).val, by
      have hh := h.memory; have hi := (sharedRowDescriptor code start).isLt
      unfold MachineCapacity.requiredSlots at hh; omega⟩).val =
      paddedCapacity m+blocks m+2^(blockSize m-1)+
        code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
        (blockSize m-1+1)+start.val*(blockSize m-1+1) := by
  simp only [sharedRowDescriptor]
  rw [arena_shared]
  let : NeZero (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) := ⟨by unfold FlatTable.words; omega⟩
  unfold sharedWords FlatTable.sharedPack
  rw [FlatTable.payload_read _ _ _ code ⟨start.val,by have := start.isLt; unfold FlatTable.words; omega⟩]
  simp only [FlatTable.sharedCells,Vector.getElem_ofFn]
  exact FlatTable.descriptor_read _ _ _ start

theorem shared_row_from_descriptor (code : Fin (2^(blockSize m-1))) (start : Fin (blockSize m-1+1)) :
    (sharedRowDescriptor code start).val =
      paddedCapacity m+blocks m+2^(blockSize m-1)+
        code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+start.val := by
  simp only [sharedRowDescriptor,sharedAddress]
  omega

theorem shared_payload_from_descriptor (code : Fin (2^(blockSize m-1)))
    (start len : Fin (blockSize m-1+1)) :
    (sharedPayload code start len).val =
      paddedCapacity m+blocks m+2^(blockSize m-1)+
        code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
        (blockSize m-1+1)+start.val*(blockSize m-1+1)+len.val := by
  simp only [sharedPayload,sharedAddress]
  omega

example : (depthAddress (m := 1) ⟨0,by decide⟩).val = 0 := by decide
example : (classAddress (m := 1) ⟨0,by decide⟩).val = 1 := by decide
example : (sharedDescriptor (m := 1) ⟨0,by decide⟩).val = 2 := by decide
example : (sharedRowDescriptor (m := 1) ⟨0,by decide⟩ ⟨0,by decide⟩).val = 3 := by decide
example : (spanAddress (m := 1) ⟨0,by decide⟩).val = 8 := by decide
example : (logAddress (m := 1) ⟨1,by decide⟩).val = 10 := by decide

end Sequences.LCA.PackedReads
