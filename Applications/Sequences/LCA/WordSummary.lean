import Applications.Sequences.LCA.WordMachine

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.WordSummary
open Resources Dijkstra.Store TreeReduction PreparationBounds PackedBackend PackedReads WordMachine

/-- Prepared offsets are backend configuration. Both descriptor and span words
are fetched from the arena; the query does not retain an abstract sparse row. -/
def logBase (m : Nat) : Nat := (logAddress (m := m) ⟨0,by omega⟩).val
def spanBase (m : Nat) : Nat := (spanAddress (m := m) ⟨0,by omega⟩).val

def run {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (start count : Nat) : Measured (Word width) Nat :=
  bind (scalar width (min start (blocks m-1))) fun si =>
  bind (scalar width (count+1)) fun len =>
  bind (scalar width (min len.val (blocks m))) fun li =>
  bind (load mem (logBase m) li.val) fun k =>
  bind (scalar width (min k.val (levels m))) fun level =>
  bind (load mem (macroBase m) level.val) fun row =>
  bind (load mem (spanBase m) level.val) fun span =>
  bind (scalar width (si.val+li.val)) fun stop =>
  bind (scalar width (stop.val-span.val)) fun second =>
  bind (scalar width (min second.val (blocks m-1))) fun right =>
  bind (load mem row.val si.val) fun a =>
  bind (load mem row.val right.val) fun b => minimum a b

theorem run_cost {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (start count : Nat) : (run m mem start count).2 = 13 := rfl

def arenaIndex {m width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (i : Fin (retainedSlots m)) : Fin capacity :=
  ⟨i.val,by have := h.memory; have := i.isLt; unfold MachineCapacity.requiredSlots at *; omega⟩

theorem load_log {m width capacity inputWords frameWords : Nat} (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) (i : Fin (blocks m+1)) :
    (load (arena input h) (logBase m) i.val).1.val = Nat.log 2 i.val := by
  rw [load_eq _ _ _ (arenaIndex h (logAddress i)) (by simp [arenaIndex,logBase,logAddress])]
  dsimp only [arenaIndex]
  rw [arena_log_read input h i, prepared_log]

theorem load_span {m width capacity inputWords frameWords : Nat} (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) (i : Fin (levels m+1)) :
    (load (arena input h) (spanBase m) i.val).1.val = 2^i.val := by
  rw [load_eq _ _ _ (arenaIndex h (spanAddress i)) (by simp [arenaIndex,spanBase,spanAddress])]
  dsimp only [arenaIndex]
  rw [arena_span_read input h i, prepared_span]

theorem load_descriptor {m width capacity inputWords frameWords : Nat} (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) (i : Fin (levels m+1)) :
    (load (arena input h) (macroBase m) i.val).1.val = macroBase m+(levels m+1)+i.val*blocks m := by
  rw [load_eq _ _ _ (arenaIndex h (macroDescriptor i)) (by simp [arenaIndex,macroDescriptor,macroAddress])]
  exact arena_macro_descriptor input h i

theorem load_payload {m width capacity inputWords frameWords : Nat} (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (load (arena input h) (macroBase m+(levels m+1)+level.val*blocks m) i.val).1.val =
      WordKey.encode 0 (paddedCapacity m)
        (ofLex ((state input).macroRows[level.val]).1[i.val]).1
        (ofLex ((state input).macroRows[level.val]).1[i.val]).2 := by
  rw [load_eq _ _ _ (arenaIndex h (macroPayload level i)) (by
    simp only [arenaIndex,macro_payload_from_descriptor])]
  simpa only [dimension,paddedCapacity,arenaIndex] using arena_macro_read input h level i

theorem macro_fits {m : Nat} (input : Input m) (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    KeyBounds.Fits 0 (2*m) (paddedCapacity m) ((state input).macroRows[level.val]).1[i.val] := by
  rw [state_eq]
  simpa only [BlockedRMQ.buildPadded,dimension,paddedCapacity,blocks,levels] using
    KeyBounds.macroCell_fits (fun j => (input.depth j : Int)) input.positive (blocks_pos m)
      (Backend.input_steps input) (depth_bounds input) (padded_le input) level i

/-- Admitted inclusive macro intervals select a prepared logarithm and its two
possibly overlapping dyadic cells. This normal form exposes exactly the cells
that the finite-word machine subsequently loads. -/
theorem summary_min {m : Nat} (input : Input m) (start count : Nat)
    (hq : start+count < blocks m) :
    BlockedRMQ.summary (state input) (blocks_pos m) start count =
      min (lookup (lookup (state input).macroRows
        ⟨Nat.log 2 (count+1), by
          have := Nat.log_mono_right (b := 2) (show count+1≤blocks m by omega)
          change Nat.log 2 (count+1) < Nat.log 2 (blocks m)+1
          omega⟩).1 ⟨start,by omega⟩)
        (lookup (lookup (state input).macroRows
        ⟨Nat.log 2 (count+1), by
          have := Nat.log_mono_right (b := 2) (show count+1≤blocks m by omega)
          change Nat.log 2 (count+1) < Nat.log 2 (blocks m)+1
          omega⟩).1
          ⟨start+(count+1)-2^Nat.log 2 (count+1),
           by have := Nat.two_pow_pos (Nat.log 2 (count+1)); omega⟩) := by
  have hs : min start (blocks m-1) = start := Nat.min_eq_left (by omega)
  have hl : min (count+1) (blocks m) = count+1 := Nat.min_eq_left (by omega)
  have hk : Nat.log 2 (count+1) ≤ levels m := Nat.log_mono_right (by omega)
  have hp := Nat.two_pow_pos (Nat.log 2 (count+1))
  have hr : min (start+(count+1)-2^Nat.log 2 (count+1)) (blocks m-1) =
      start+(count+1)-2^Nat.log 2 (count+1) := Nat.min_eq_left (by omega)
  have hlog := prepared_log input ⟨count+1,by omega⟩
  have hspan := prepared_span input ⟨Nat.log 2 (count+1),by omega⟩
  simp only [BlockedRMQ.summary, SparseExecution.query, Resources.bind, TableExecution.read,
    lookup, hs, hl, hlog, Nat.min_eq_left hk, hspan, hr]


theorem summary_fits {m : Nat} (input : Input m) (start count : Nat)
    (hq : start+count < blocks m) :
    KeyBounds.Fits 0 (2*m) (paddedCapacity m)
      (BlockedRMQ.summary (state input) (blocks_pos m) start count) := by
  rw [summary_min input start count hq]
  apply KeyBounds.fits_min
  · exact macro_fits input _ _
  · exact macro_fits input _ _


theorem run_value {m width capacity inputWords frameWords : Nat} (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (start count : Nat) (hq : start+count < blocks m) :
    (run m (arena input h) start count).1.val =
      WordKey.encode 0 (paddedCapacity m)
        (ofLex (BlockedRMQ.summary (state input) (blocks_pos m) start count)).1
        (ofLex (BlockedRMQ.summary (state input) (blocks_pos m) start count)).2 := by
  let k := Nat.log 2 (count+1)
  have hk : k ≤ levels m := Nat.log_mono_right (by omega)
  have hpow : 0<2^k := Nat.two_pow_pos k
  have hright : start+(count+1)-2^k < blocks m := by omega
  let level : Fin (levels m+1) := ⟨k,by omega⟩
  let left : Fin (blocks m) := ⟨start,by omega⟩
  let right : Fin (blocks m) := ⟨start+(count+1)-2^k,hright⟩
  have fit (x : Nat) (hx : x ≤ blocks m) : (word width x).val = x := by
    apply word_of_lt
    apply MachineCapacity.scalar_fits h.toWordEligible
    have := blocks_le input.positive
    omega
  have fs := fit start (by omega)
  have fl := fit (count+1) (by omega)
  have fk := fit k (by have := Nat.log_le_self 2 (count+1); dsimp [k]; omega)
  have fend := fit (start+(count+1)) (by omega)
  have fr := fit (start+(count+1)-2^k) (by omega)
  have hlog := load_log input h (⟨count+1,by omega⟩ : Fin (blocks m+1))
  have hspan := load_span input h level
  have hdesc := load_descriptor input h level
  have ha := load_payload input h level left
  have hb := load_payload input h level right
  have hfa := macro_fits input level left
  have hfb := macro_fits input level right
  dsimp only [level, left, right, k] at hk hright hpow fs fl fk fend fr hspan hdesc ha hb hfa hfb ⊢
  rw [summary_min input start count hq]
  dsimp only [lookup]
  rw [WordKey.encode_min hfa.1 hfb.1 hfa.2.2 hfb.2.2]
  simp only [run, Resources.bind, scalar, minimum]
  simp only [Nat.min_eq_left (show start≤blocks m-1 by omega), fs, fl,
    Nat.min_eq_left (show count+1≤blocks m by omega), hlog,
    Nat.min_eq_left hk, fk, hdesc, hspan, fend, fr,
    Nat.min_eq_left (show start+(count+1)-2^Nat.log 2 (count+1)≤blocks m-1 by omega)]
  change min _ _ = _
  rw [ha, hb]

end Sequences.LCA.WordSummary
