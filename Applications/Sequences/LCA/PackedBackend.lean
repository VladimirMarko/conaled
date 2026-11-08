import Applications.Sequences.LCA.Backend
import Applications.Sequences.LCA.FlatTable
import Applications.Sequences.LCA.MachineCapacity

/-! Instantiate the word interpretation on the actual prepared backend state.
All payload encodings are finite words. Descriptor layouts come from FlatTable;
these are representation maps, not additional preprocessing passes. -/
namespace Sequences.LCA.PackedBackend
open PreparationBounds TreeReduction Dijkstra.Store
variable {m width capacity : Nat}

def state (input : Input m) := ((Backend.ops m).prepare input).1

theorem state_eq (input : Input m) : state input =
    BlockedRMQ.buildPadded (fun i => (input.depth i : Int)) m (blockSize m-1) :=
  Backend.prepare_valid input

theorem depth_bounds (input : Input m) (i : Nat) (hi : i < m) :
    0 ≤ (input.depth i : Int) ∧ (input.depth i : Int) < (m : Int) := by
  have hh := input.bounded ⟨i,hi⟩
  simp only [Input.depth, hi, dite_true]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hh⟩

theorem dimension (m : Nat) : blockSize m-1+1 = blockSize m := by
  have := blockSize_pos m
  omega

theorem padded_le (input : Input m) : blocks m*(blockSize m-1+1) ≤ 2*m := by
  rw [dimension]
  exact paddedCapacity_le input.positive

theorem prepared_shared (input : Input m) :
    (state input).micro.shared = prepareShared (blockSize m-1) := by
  rw [state_eq]
  rfl

theorem prepared_depth (input : Input m) (i : Fin (blocks m*(blockSize m-1+1))) :
    (state input).micro.depths[i.val] = paddedDepth (fun j => (input.depth j : Int)) m i.val := by
  rw [state_eq]
  simp only [BlockedRMQ.buildPadded, BlockedRMQ.build, BlockedRMQ.buildMicro]
  erw [Vector.getElem_ofFn]

def depthWords (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    Vector (Fin (2^width)) (blocks m*(blockSize m-1+1)) :=
  Vector.ofFn fun i => ⟨((state input).micro.depths[i.val]).toNat, by
    have hb := KeyBounds.paddedDepth_bounds (fun j => (input.depth j : Int)) input.positive
      (depth_bounds input) (padded_le input) i.isLt
    rw [prepared_depth]
    apply MachineCapacity.scalar_fits h
    omega⟩

theorem depthWords_read (input : Input m) (h : MachineCapacity.WordEligible m width capacity)
    (i : Fin (blocks m*(blockSize m-1+1))) :
    (((depthWords input h)[i.val]).val : Int) = (state input).micro.depths[i.val] := by
  have hb := KeyBounds.paddedDepth_bounds (fun j => (input.depth j : Int)) input.positive
    (depth_bounds input) (padded_le input) i.isLt
  simp only [depthWords, Vector.getElem_ofFn]
  rw [prepared_depth]
  exact Int.toNat_of_nonneg hb.1

def classWords (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    Vector (Fin (2^width)) (blocks m) :=
  (state input).micro.classes.map (fun c => ⟨c.val,
    c.isLt.trans (MachineCapacity.class_count_fits h)⟩)

theorem classWords_read (input : Input m) (h : MachineCapacity.WordEligible m width capacity)
    (i : Fin (blocks m)) :
    ((classWords input h)[i.val]).val = ((state input).micro.classes[i.val]).val := by
  simp [classWords]

def macroWords (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    Vector (Vector (Fin (2^width)) (blocks m)) (levels m+1) :=
  FlatTable.macroMatrix (fun i => (input.depth i : Int)) input.positive (blocks_pos m)
    (Backend.input_steps input) (depth_bounds input) (padded_le input)
    ((KeyBounds.macro_capacity_le (padded_le input)).trans h.keys)

theorem macroWords_read (input : Input m) (h : MachineCapacity.WordEligible m width capacity)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    ((macroWords input h)[level.val][i.val]).val =
      WordKey.encode 0 (blocks m*(blockSize m-1+1))
        (ofLex ((state input).macroRows[level.val]).1[i.val]).1
        (ofLex ((state input).macroRows[level.val]).1[i.val]).2 := by
  rw [state_eq]
  exact FlatTable.macroMatrix_read _ _ _ _ _ _ _ level i

theorem prepared_span (input : Input m) (level : Fin (levels m+1)) :
    ((state input).macroRows[level.val]).2 = 2^level.val := by
  rw [state_eq]
  simp only [BlockedRMQ.buildPadded, BlockedRMQ.build, SparseExecution.prepare,
    Resources.bind, Resources.pure]
  erw [SparseExecution.build_get]

theorem prepared_log (input : Input m) (i : Fin (blocks m+1)) :
    (state input).macroLogs[i.val] = Nat.log 2 i.val := by
  rw [state_eq]
  exact SparseExecution.logs_get _ i

def spanWords (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    Vector (Fin (2^width)) (levels m+1) :=
  Vector.ofFn fun level => ⟨((state input).macroRows[level.val]).2, by
    rw [prepared_span]
    have hl : level.val ≤ levels m := by have := level.isLt; omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl
    have hk := Nat.pow_log_le_self 2 (Nat.ne_of_gt (blocks_pos m))
    have hb := blocks_le input.positive
    apply MachineCapacity.scalar_fits h
    unfold levels at hp
    omega⟩

def logWords (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    Vector (Fin (2^width)) (blocks m+1) :=
  Vector.ofFn fun i => ⟨(state input).macroLogs[i.val], by
    rw [prepared_log]
    have hh := Nat.log_le_self 2 i.val
    have hb := blocks_le input.positive
    apply MachineCapacity.scalar_fits h
    have hi := i.isLt
    omega⟩

theorem spanWords_read (input : Input m) (h : MachineCapacity.WordEligible m width capacity)
    (level : Fin (levels m+1)) :
    ((spanWords input h)[level.val]).val = ((state input).macroRows[level.val]).2 := by
  simp [spanWords]

theorem logWords_read (input : Input m) (h : MachineCapacity.WordEligible m width capacity)
    (i : Fin (blocks m+1)) :
    ((logWords input h)[i.val]).val = (state input).macroLogs[i.val] := by simp [logWords]


theorem micro_width (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    (2*(blockSize m-1)+1)*(2*(blockSize m-1+1)) ≤ 2^width := by
  rw [dimension]
  exact (KeyBounds.micro_capacity_le (blockSize_le input.positive)).trans h.keys

theorem shared_fit (_input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    paddedCapacity m + blocks m +
      FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)) ≤ capacity := by
  rw [FlatTable.sharedPack_size, dimension]
  have hh := h.memory
  unfold MachineCapacity.requiredSlots PreparationBounds.retainedSlots PreparationBounds.sharedSlots at hh
  omega

def sharedWords (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :=
  FlatTable.sharedPack (blockSize m-1) (paddedCapacity m+blocks m) capacity
    (micro_width input h.toWordEligible) (shared_fit input h) h.addresses

theorem sharedWords_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    ((sharedWords input h)[2^(blockSize m-1)+
      code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
      ((blockSize m-1+1)+start.val*(blockSize m-1+1)+len.val)]'
        (FlatTable.payload_index_lt code ⟨_,FlatTable.payload_index_lt start len⟩)).val =
      WordKey.encode ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1))
        (ofLex ((((state input).micro.shared.get code).get start).get len)).1
        (ofLex ((((state input).micro.shared.get code).get start).get len)).2 := by
  unfold sharedWords
  rw [FlatTable.sharedPack_payload, FlatTable.microMatrix_read, prepared_shared]

def macroBase (m : Nat) := paddedCapacity m+blocks m+sharedSlots m+blocks m

theorem macro_fit (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    macroBase m + FlatTable.words (levels m+1) (blocks m) ≤ capacity := by
  have hh := h.memory
  unfold MachineCapacity.requiredSlots retainedSlots SparseExecution.retainedSlots at hh
  unfold macroBase FlatTable.words
  nlinarith

def macroPack (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :=
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  FlatTable.pack (macroWords input h.toWordEligible) (macroBase m) capacity
    (macro_fit h) h.addresses

theorem macroPack_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    ((macroPack input h)[(levels m+1)+level.val*blocks m+i.val]'
      (FlatTable.payload_index_lt level i)).val =
      WordKey.encode 0 (blocks m*(blockSize m-1+1))
        (ofLex ((state input).macroRows[level.val]).1[i.val]).1
        (ofLex ((state input).macroRows[level.val]).1[i.val]).2 := by
  let : NeZero (blocks m) := ⟨Nat.ne_of_gt (blocks_pos m)⟩
  unfold macroPack
  rw [FlatTable.payload_read, macroWords_read]

/-- Every retained field is a finite word vector. The descriptor-bearing
shared and macro fields use their actual global arena bases. -/
structure Representation (m width : Nat) where
  depths : Vector (Fin (2^width)) (blocks m*(blockSize m-1+1))
  classes : Vector (Fin (2^width)) (blocks m)
  shared : Vector (Fin (2^width))
    (FlatTable.words (2^(blockSize m-1)) (FlatTable.words (blockSize m-1+1) (blockSize m-1+1)))
  macroTable : Vector (Fin (2^width)) (FlatTable.words (levels m+1) (blocks m))
  spans : Vector (Fin (2^width)) (levels m+1)
  logs : Vector (Fin (2^width)) (blocks m+1)

def realize (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : Representation m width :=
  ⟨depthWords input h.toWordEligible, classWords input h.toWordEligible,
    sharedWords input h, macroPack input h, spanWords input h.toWordEligible,
    logWords input h.toWordEligible⟩

def Representation.flatten (r : Representation m width) :
    Vector (Fin (2^width)) (retainedSlots m) :=
  (r.depths ++ r.classes ++ r.shared ++
    Vector.replicate (blocks m) (⟨0, Nat.two_pow_pos width⟩ : Fin (2^width)) ++
    r.macroTable ++ r.spans ++ r.logs).cast (by
      rw [FlatTable.sharedPack_size, dimension]
      unfold retainedSlots paddedCapacity sharedSlots SparseExecution.retainedSlots FlatTable.words
      ring)

def arena (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) : Store capacity (Fin (2^width)) :=
  Arena.install (⟨0, by have := h.memory; unfold MachineCapacity.requiredSlots at this; omega⟩ :
      Arena.Segment capacity (retainedSlots m))
    (realize input h).flatten (Arena.initialized capacity width)

theorem arena_read (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (retainedSlots m)) :
    lookup (arena input h) ⟨i.val, by
      have hh := h.memory
      have hi := i.isLt
      unfold MachineCapacity.requiredSlots at hh
      omega⟩ = ((realize input h).flatten)[i.val] := by
  let seg : Arena.Segment capacity (retainedSlots m) := ⟨0, by
    have hh := h.memory
    unfold MachineCapacity.requiredSlots at hh
    omega⟩
  have hh := Arena.install_represents seg (realize input h).flatten
    (Arena.initialized capacity width) i
  simpa [arena, seg, Arena.Segment.address, lookup] using hh

/-- This observation counts the actual finite output vector, including the
reserved block-minimum gap. Temporary allocation regions are disjoint. -/
theorem flattened_size (r : Representation m width) : r.flatten.toArray.size = retainedSlots m :=
  Vector.size_toArray _


private def singletonInput : Input 1 where
  cells := #v[(0,0)]
  positive := by decide
  bounded i := by have : i=0 := Fin.eq_zero i; subst i; decide
  identityBound i := by have : i=0 := Fin.eq_zero i; subst i; decide
  unit i hi := by omega

private theorem singletonMachine : MachineCapacity.Eligible 1 8 128 2 64 := by
  constructor
  · constructor <;> decide
  · decide

example : ((realize singletonInput singletonMachine).depths[0]).val = 0 := by
  simp [realize, depthWords, prepared_depth, singletonInput, Input.depth, paddedDepth, lookup]

example : ((realize singletonInput singletonMachine).spans[0]).val = 1 := by
  simp [realize, spanWords, prepared_span]

end Sequences.LCA.PackedBackend
