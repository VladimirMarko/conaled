import Applications.Sequences.LCA.WordMachine

/-! Actual finite-word loads from the prepared arena, including the pointer
values used as bases for the next load. Each equality proves the totalized
load takes its in-range branch. -/
namespace Sequences.LCA.WordLoads
open PreparationBounds PackedBackend PackedReads TreeReduction Dijkstra.Store WordMachine
variable {m width capacity inputWords frameWords : Nat}

theorem load_address (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (base index : Nat) (i : Fin (retainedSlots m)) (he : base+index=i.val) :
    (load (arena input h) base index).1 =
      lookup (arena input h) ⟨i.val, by
        have hh := h.memory; have hi := i.isLt
        unfold MachineCapacity.requiredSlots at hh; omega⟩ := by
  exact load_eq _ base index _ he

theorem load_depth (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (blocks m*(blockSize m-1+1))) :
    ((load (arena input h) (0) i.val).1.val : Int) = (state input).micro.depths[i.val] := by
  rw [load_address input h _ _ (depthAddress i) (by
    simp only [depthAddress]
    omega)]
  exact arena_depth_read input h i

theorem load_class (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (blocks m)) :
    (load (arena input h) (paddedCapacity m) i.val).1.val = ((state input).micro.classes[i.val]).val := by
  rw [load_address input h _ _ (PackedReads.classAddress i) (by
    rfl)]
  exact arena_class_read input h i

theorem load_span (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (levels m+1)) :
    (load (arena input h) (macroBase m+FlatTable.words (levels m+1) (blocks m)) i.val).1.val = ((state input).macroRows[i.val]).2 := by
  rw [load_address input h _ _ (spanAddress i) (by
    rfl)]
  exact arena_span_read input h i

theorem load_log (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (blocks m+1)) :
    (load (arena input h) (macroBase m+FlatTable.words (levels m+1) (blocks m)+(levels m+1)) i.val).1.val = (state input).macroLogs[i.val] := by
  rw [load_address input h _ _ (logAddress i) (by
    rfl)]
  exact arena_log_read input h i

theorem load_sharedDescriptor (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) :
    (load (arena input h) (paddedCapacity m+blocks m) code.val).1.val = paddedCapacity m+blocks m+2^(blockSize m-1)+code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1) := by
  rw [load_address input h _ _ (sharedDescriptor code) (by
    rfl)]
  exact arena_shared_descriptor input h code

theorem load_sharedRowDescriptor (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start : Fin (blockSize m-1+1)) :
    (load (arena input h) (paddedCapacity m+blocks m+2^(blockSize m-1)+code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) start.val).1.val = paddedCapacity m+blocks m+2^(blockSize m-1)+code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+(blockSize m-1+1)+start.val*(blockSize m-1+1) := by
  rw [load_address input h _ _ (sharedRowDescriptor code start) (by
    simp only [sharedRowDescriptor,sharedAddress]
    omega)]
  exact arena_shared_row_descriptor input h code start

theorem load_sharedPayload (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    (load (arena input h) (paddedCapacity m+blocks m+2^(blockSize m-1)+code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+(blockSize m-1+1)+start.val*(blockSize m-1+1)) len.val).1.val = WordKey.encode ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1))
      (ofLex ((((state input).micro.shared.get code).get start).get len)).1
      (ofLex ((((state input).micro.shared.get code).get start).get len)).2 := by
  rw [load_address input h _ _ (sharedPayload code start len) (by
    simp only [sharedPayload,sharedAddress]
    omega)]
  exact arena_shared_read input h code start len

theorem load_macroDescriptor (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) :
    (load (arena input h) (macroBase m) level.val).1.val = macroBase m+(levels m+1)+level.val*blocks m := by
  rw [load_address input h _ _ (macroDescriptor level) (by
    rfl)]
  exact arena_macro_descriptor input h level

theorem load_macroPayload (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (load (arena input h) (macroBase m+(levels m+1)+level.val*blocks m) i.val).1.val = WordKey.encode 0 (blocks m*(blockSize m-1+1))
      (ofLex ((state input).macroRows[level.val]).1[i.val]).1
      (ofLex ((state input).macroRows[level.val]).1[i.val]).2 := by
  rw [load_address input h _ _ (macroPayload level i) (by
    simp only [macroPayload,macroAddress]
    omega)]
  exact arena_macro_read input h level i

end Sequences.LCA.WordLoads
