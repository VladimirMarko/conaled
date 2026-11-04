import Applications.Sequences.LCA.WordLoads

set_option maxHeartbeats 2000000

namespace Sequences.LCA.WordWithin
open Resources PreparationBounds PackedBackend Dijkstra.Store
variable {m width capacity : Nat}

def within (m : Nat) (mem : Store capacity (WordMachine.Word width))
    (block offset len : Nat) : Measured (WordMachine.Word width) Nat :=
  bind (WordMachine.scalar width (min block (blocks m-1))) fun bi =>
  bind (WordMachine.load mem (paddedCapacity m) bi.val) fun code =>
  bind (WordMachine.scalar width (min offset (blockSize m-1))) fun oi =>
  bind (WordMachine.scalar width (min len (blockSize m-1))) fun li =>
  bind (WordMachine.load mem (paddedCapacity m+blocks m) code.val) fun table =>
  bind (WordMachine.load mem table.val oi.val) fun row =>
  bind (WordMachine.load mem row.val li.val) fun key =>
  bind (WordMachine.scalar width (key.val % (2*blockSize m))) fun relativeIndex =>
  bind (WordMachine.scalar width (block*blockSize m)) fun base =>
  bind (WordMachine.scalar width (base.val+relativeIndex.val)) fun global =>
  bind (WordMachine.scalar width (min global.val (paddedCapacity m-1))) fun gi =>
  bind (WordMachine.load mem 0 gi.val) fun depth =>
  WordMachine.pack (paddedCapacity m) depth global

theorem within_cost (m : Nat) (mem : Store capacity (WordMachine.Word width))
    (block offset len : Nat) : (within m mem block offset len).2 = 14 := rfl

theorem within_semantic (input : TreeReduction.Input m) (hblock : block < blocks m)
    (hinterval : offset+len < blockSize m) :
    BlockedRMQ.within (state input).micro (blocks_pos m) block offset len =
      PreparedRMQ.rangeMin (depthKey (paddedDepth (fun i => (input.depth i : Int)) m))
        (block*blockSize m+offset) len := by
  rw [state_eq]
  have hh := BlockedRMQ.within_build
    (paddedDepth (fun i => (input.depth i : Int)) m) (blocks_pos m)
    (fun block _ => by simpa only [dimension] using padded_block_steps _ input.positive (Backend.input_steps input) block (blockSize m))
    hblock (show offset+len ≤ blockSize m-1 by omega)
  simpa only [BlockedRMQ.buildPadded,BlockedRMQ.build,PreparationBounds.blocks,dimension] using hh

theorem within_fits (input : TreeReduction.Input m) (hblock : block < blocks m)
    (hinterval : offset+len < blockSize m) :
    KeyBounds.Fits 0 (2*m) (paddedCapacity m)
      (BlockedRMQ.within (state input).micro (blocks_pos m) block offset len) := by
  rw [within_semantic input hblock hinterval]
  apply KeyBounds.rangeMin_fits
  intro i hi
  apply KeyBounds.paddedKey_fits _ input.positive (depth_bounds input) (paddedCapacity_le input.positive)
  have hm := Nat.mul_le_mul_right (blockSize m) (show block+1 ≤ blocks m by omega)
  unfold paddedCapacity
  nlinarith

private theorem scalar_value (hi : i < 2^width) : (WordMachine.scalar width i).1.val = i :=
  WordMachine.word_of_lt hi

theorem within_value (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (hblock : block < blocks m) (hinterval : offset+len < blockSize m) :
    (within m (arena input h) block offset len).1.val =
      WordKey.encode 0 (paddedCapacity m)
        (ofLex (BlockedRMQ.within (state input).micro (blocks_pos m) block offset len)).1
        (ofLex (BlockedRMQ.within (state input).micro (blocks_pos m) block offset len)).2 := by
  have hb := blockSize_pos m
  have hbn := blockSize_le input.positive
  have hkn := blocks_le input.positive
  have hpn := paddedCapacity_le input.positive
  have hbi : min block (blocks m-1) = block := min_eq_left (by omega)
  have hoi : min offset (blockSize m-1) = offset := min_eq_left (by omega)
  have hli : min len (blockSize m-1) = len := min_eq_left (by omega)
  let code := (state input).micro.classes[block]
  let oi : Fin (blockSize m-1+1) := ⟨offset,by omega⟩
  let li : Fin (blockSize m-1+1) := ⟨len,by omega⟩
  let key := ((((state input).micro.shared.get code).get oi).get li)
  let relativeIndex := (ofLex key).2
  let global := block*blockSize m+relativeIndex
  have hf := within_fits input hblock hinterval
  have hs : BlockedRMQ.within (state input).micro (blocks_pos m) block offset len =
      depthKey (BlockedRMQ.readDepth (state input).micro (blocks_pos m)) global := by
    simp only [BlockedRMQ.within,hbi,hoi,hli,dimension,lookupShared,lookupClass]
    rfl
  have hg : global < paddedCapacity m := by
    rw [hs] at hf
    exact hf.2.2
  let gi : Fin (blocks m*(blockSize m-1+1)) := ⟨global,by simpa only [dimension,paddedCapacity] using hg⟩
  have hd : BlockedRMQ.readDepth (state input).micro (blocks_pos m) global =
      (state input).micro.depths[gi.val] := by
    simp only [BlockedRMQ.readDepth]
    have he : min global (blocks m*(blockSize m-1+1)-1) = global := by rw [dimension]; exact min_eq_left (by unfold paddedCapacity at hg; omega)
    simp only [he]
    rfl
  have hheight : 0 ≤ (state input).micro.depths[gi.val] ∧
      (state input).micro.depths[gi.val] < (2*m : Nat) := by
    rw [hs] at hf
    simpa only [KeyBounds.Fits,depthKey,ofLex_toLex,Int.add_zero,hd] using And.intro hf.1 hf.2.1
  have hlocal : relativeIndex < 2*blockSize m := by
    have hk := KeyBounds.sharedCell_fits code oi li
    rw [← prepared_shared input] at hk
    simpa only [dimension] using hk.2.2
  have hdecode : WordKey.encode ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1+1))
      (ofLex key).1 (ofLex key).2 % (2*blockSize m) = relativeIndex := by
    simp only [dimension,WordKey.encode]
    exact WordKey.pack_mod hlocal
  have hbword : block < 2^width := MachineCapacity.scalar_fits h.toWordEligible (by omega)
  have howord : offset < 2^width := MachineCapacity.scalar_fits h.toWordEligible (by omega)
  have hlword : len < 2^width := MachineCapacity.scalar_fits h.toWordEligible (by omega)
  have hrword : relativeIndex < 2^width := MachineCapacity.scalar_fits h.toWordEligible (by omega)
  have hbaseword : block*blockSize m < 2^width := MachineCapacity.scalar_fits h.toWordEligible (by change block*blockSize m+relativeIndex < paddedCapacity m at hg; omega)
  have hgword : global < 2^width := MachineCapacity.scalar_fits h.toWordEligible (by omega)
  have hclip : min global (paddedCapacity m-1) = global := min_eq_left (by omega)
  have hcode := WordLoads.load_class input h (⟨block,hblock⟩ : Fin (blocks m))
  have htable := WordLoads.load_sharedDescriptor input h code
  have hrow := WordLoads.load_sharedRowDescriptor input h code oi
  have hkey := WordLoads.load_sharedPayload input h code oi li
  have hdepth := WordLoads.load_depth input h gi
  have hdepthnat : (WordMachine.load (arena input h) 0 global).1.val =
      ((state input).micro.depths[gi.val]).toNat := by
    have hh := congrArg Int.toNat hdepth
    simpa using hh
  have hsum : ((state input).micro.depths[gi.val]).toNat*paddedCapacity m+global < 2^width := by
    apply lt_of_lt_of_le (WordKey.pack_lt_capacity hg (heights := 2*m) (by omega))
    exact (KeyBounds.macro_capacity_le hpn).trans h.keys
  rw [hs]
  simp only [depthKey,ofLex_toLex,hd,WordKey.encode,Int.add_zero,WordKey.pack]
  simp only [within,Resources.bind,hbi,hoi,hli,scalar_value hbword,scalar_value howord,scalar_value hlword]
  rw [hcode,htable,hrow,hkey]
  rw [hdecode,scalar_value hrword,scalar_value hbaseword]
  change (WordMachine.pack (paddedCapacity m)
    (WordMachine.load (arena input h) 0
      (WordMachine.scalar width (min (WordMachine.scalar width global).1.val (paddedCapacity m-1))).1.val).1
    (WordMachine.scalar width global).1).1.val = _
  rw [scalar_value hgword,hclip,scalar_value hgword]
  rw [WordMachine.pack_value]
  · rw [hdepthnat,scalar_value hgword]
  · rw [hdepthnat]; omega
  · rw [hdepthnat,scalar_value hgword]; exact hsum

/-- The first singleton interval exercises the same full packed lookup path. -/
example (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) :
    (within m (arena input h) 0 0 0).1.val =
      WordKey.encode 0 (paddedCapacity m)
        (ofLex (BlockedRMQ.within (state input).micro (blocks_pos m) 0 0 0)).1
        (ofLex (BlockedRMQ.within (state input).micro (blocks_pos m) 0 0 0)).2 :=
  within_value input h (blocks_pos m) (blockSize_pos m)

end Sequences.LCA.WordWithin
