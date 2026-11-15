import Applications.Sequences.LCA.PreparationInvariants
import Applications.Sequences.LCA.TableTransport
import Applications.Sequences.LCA.PackedBackend
import Applications.Sequences.LCA.Control
import Applications.Sequences.LCA.WordMachine

/-! Executed finite-cell preparation refines the raw key programs. Source
lifting defaults only outside the visited prefix; both output and primitive
cost are transported through every initialized and updated row. -/
namespace Sequences.LCA.PreparationCertificate
open Resources Dijkstra.Store KeyBounds TableTransport
abbrev Cell := WordKey.Cell

variable {offset : Int} {heights stride n m width capacity inputWords frameWords : Nat}

def encodeKey (key : Key) := WordKey.encode offset stride (ofLex key).1 (ofLex key).2

theorem cell_val_min (a b : Cell offset heights stride) :
    (min a b).val = min a.val b.val := by
  by_cases h : a ≤ b
  · rw [min_eq_left h,min_eq_left (show a.val ≤ b.val from h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right (show b.val ≤ a.val from le_of_not_ge h)]

def liftSource (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (len : Nat) (hs : ∀ i, i < len → Fits offset heights stride (source i).1)
    (i : Nat) : Measured (Cell offset heights stride) Nat :=
  (if hi : i < len then ⟨(source i).1,hs i hi⟩ else seed,(source i).2)

theorem liftSource_at (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (len : Nat) (hs : ∀ i, i < len → Fits offset heights stride (source i).1)
    (i : Nat) (hi : i < len) :
    transport Subtype.val (liftSource seed source len hs i) = source i := by
  simp [transport,liftSource,hi]

theorem liftedRow_erases (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (capacity len : Nat) (hl : len ≤ capacity)
    (hs : ∀ i, i < len → Fits offset heights stride (source i).1) :
    transport (Vector.map Subtype.val)
      (MicroExecution.rowFill seed (liftSource seed source len hs) capacity len hl) =
      MicroExecution.rowFill seed.val source capacity len hl := by
  rw [← rowFill_transport Subtype.val cell_val_min]
  apply rowFill_congr_source
  exact liftSource_at seed source len hs

def wordRow (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (capacity len : Nat) (hl : len ≤ capacity)
    (hs : ∀ i, i < len → Fits offset heights stride (source i).1) :=
  MicroExecution.rowFill (WordKey.cellWord seed)
    (fun i => transport WordKey.cellWord (liftSource seed source len hs i)) capacity len hl

theorem wordRow_transport (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (capacity len : Nat) (hl : len ≤ capacity)
    (hs : ∀ i, i < len → Fits offset heights stride (source i).1) :
    wordRow seed source capacity len hl hs =
      transport (Vector.map WordKey.cellWord)
        (MicroExecution.rowFill seed (liftSource seed source len hs) capacity len hl) :=
  rowFill_transport WordKey.cellWord WordKey.cellWord_min seed _ capacity len hl

theorem wordRow_refines (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (capacity len : Nat) (hl : len ≤ capacity)
    (hs : ∀ i, i < len → Fits offset heights stride (source i).1) :
    transport (Vector.map Fin.val) (wordRow seed source capacity len hl hs) =
      transport (Vector.map (encodeKey (offset := offset) (stride := stride)))
        (MicroExecution.rowFill seed.val source capacity len hl) := by
  rw [wordRow_transport,← liftedRow_erases seed source capacity len hl hs]
  simp [transport,Vector.map_map,Function.comp_def,WordKey.cellWord,encodeKey]

theorem wordRow_cost (seed : Cell offset heights stride) (source : Nat → Measured Key Nat)
    (capacity len : Nat) (hl : len ≤ capacity)
    (hs : ∀ i, i < len → Fits offset heights stride (source i).1) :
    (wordRow seed source capacity len hl hs).2 =
      (MicroExecution.rowFill seed.val source capacity len hl).2 :=
  congrArg Prod.snd (wordRow_refines seed source capacity len hl hs)

def liftVector (input : Vector Key n)
    (hi : ∀ i : Fin n, Fits offset heights stride input[i.val]) : Vector (Cell offset heights stride) n :=
  Vector.ofFn fun i => ⟨input[i.val],hi i⟩

theorem liftVector_erases (input : Vector Key n)
    (hi : ∀ i : Fin n, Fits offset heights stride input[i.val]) :
    (liftVector input hi).map Subtype.val = input := by
  apply Vector.ext
  intro i hi'
  simp [liftVector]

def wordSparse (seed : Cell offset heights stride) (input : Vector Key n)
    (hi : ∀ i : Fin n, Fits offset heights stride input[i.val]) (levels : Nat) :=
  SparseExecution.prepare (WordKey.cellWord seed) (WordKey.encodeStore (liftVector input hi)) levels

theorem liftedSparse_erases (seed : Cell offset heights stride) (input : Vector Key n)
    (hi : ∀ i : Fin n, Fits offset heights stride input[i.val]) (levels : Nat) :
    transport (fun pair => (rowsMap Subtype.val pair.1,pair.2))
      (SparseExecution.prepare seed (liftVector input hi) levels) =
      SparseExecution.prepare seed.val input levels := by
  rw [← sparsePrepare_transport Subtype.val cell_val_min,liftVector_erases]

theorem wordSparse_refines (seed : Cell offset heights stride) (input : Vector Key n)
    (hi : ∀ i : Fin n, Fits offset heights stride input[i.val]) (levels : Nat) :
    transport (fun pair => (rowsMap Fin.val pair.1,pair.2)) (wordSparse seed input hi levels) =
      transport (fun pair => (rowsMap (encodeKey (offset := offset) (stride := stride)) pair.1,pair.2))
        (SparseExecution.prepare seed.val input levels) := by
  unfold wordSparse
  rw [wordSparsePrepare,← liftedSparse_erases seed input hi levels]
  simp [transport,rowsMap,Vector.map_map,Function.comp_def,WordKey.cellWord,encodeKey]

theorem wordSparse_cost (seed : Cell offset heights stride) (input : Vector Key n)
    (hi : ∀ i : Fin n, Fits offset heights stride input[i.val]) (levels : Nat) :
    (wordSparse seed input hi levels).2 = (SparseExecution.prepare seed.val input levels).2 :=
  congrArg Prod.snd (wordSparse_refines seed input hi levels)

def microSeed (steps code : Nat) : Cell (steps : Int) (2*steps+1) (2*(steps+1)) :=
  ⟨(MicroExecution.keySource (canonicalHeights steps code) 0 0).1,
    PreparationInvariants.keySource_fits steps code 0 0 (by omega) (by omega)⟩

def microRow (steps code : Nat) (start : Fin (steps+1)) (len : Nat) (hl : len ≤ steps+1) :=
  wordRow (microSeed steps code) (MicroExecution.keySource (canonicalHeights steps code) start.val)
    (steps+1) len hl (fun i hi => PreparationInvariants.keySource_fits steps code start.val i start.isLt (by omega))

theorem microRow_refines (steps code : Nat) (start : Fin (steps+1)) (len : Nat) (hl : len ≤ steps+1) :
    transport (Vector.map Fin.val) (microRow steps code start len hl) =
      transport (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1))))
        (MicroExecution.rowFill (MicroExecution.keySource (canonicalHeights steps code) 0 0).1
          (MicroExecution.keySource (canonicalHeights steps code) start.val) (steps+1) len hl) :=
  wordRow_refines _ _ _ _ _ _

/-- Bounds on a materialized canonical height array, retained as proof data. -/
def HeightDomain (steps : Nat) (heights : Heights steps) : Prop :=
  ∀ i, -(steps : Int) ≤ boundedDepth heights i ∧ boundedDepth heights i ≤ (steps : Int)

theorem heightSource_fits (heights : Heights steps) (hh : HeightDomain steps heights)
    (start i : Nat) (hs : start < steps+1) (hi : i < steps+1) :
    Fits (steps : Int) (2*steps+1) (2*(steps+1)) (MicroExecution.keySource heights start i).1 := by
  rw [MicroExecution.keySource_exact]
  have hd := hh (start+i)
  simp only [Fits,depthKey,ofLex_toLex]
  exact ⟨by omega,by omega,by omega⟩

def classSeed (heights : Heights steps) (hh : HeightDomain steps heights) :
    Cell (steps : Int) (2*steps+1) (2*(steps+1)) :=
  ⟨(MicroExecution.keySource heights 0 0).1,heightSource_fits heights hh 0 0 (by omega) (by omega)⟩

def classProgram (heights : Heights steps) (hh : HeightDomain steps heights) :=
  bind (WordKey.cellWord (classSeed heights hh),(MicroExecution.keySource heights 0 0).2) fun seed =>
  bind (TableExecution.initStore seed (steps+1)) fun seedRow =>
  TableExecution.tabulate seedRow (fun start : Fin (steps+1) =>
    wordRow (classSeed heights hh) (MicroExecution.keySource heights start.val) (steps+1) (steps+1) le_rfl
      (fun i hi => heightSource_fits heights hh start.val i start.isLt hi))

theorem classProgram_refines (heights : Heights steps) (hh : HeightDomain steps heights) :
    transport (Vector.map (Vector.map Fin.val)) (classProgram heights hh) =
      transport (Vector.map (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1)))))
        (MicroExecution.buildClassM heights) := by
  simp only [classProgram,MicroExecution.buildClassM,Resources.bind,TableExecution.initStore_exact]
  have hw := fun start : Fin (steps+1) =>
    wordRow_refines (classSeed heights hh) (MicroExecution.keySource heights start.val)
      (steps+1) (steps+1) le_rfl (fun i hi => heightSource_fits heights hh start.val i start.isLt hi)
  have ht := tabulate_transport (Vector.map Fin.val)
    (Vector.replicate (steps+1) (WordKey.cellWord (classSeed heights hh)))
    (fun start : Fin (steps+1) => wordRow (classSeed heights hh)
      (MicroExecution.keySource heights start.val) (steps+1) (steps+1) le_rfl
      (fun i hi => heightSource_fits heights hh start.val i start.isLt hi))
  have he := tabulate_transport
    (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1))))
    (Vector.replicate (steps+1) (MicroExecution.keySource heights 0 0).1)
    (fun start : Fin (steps+1) => MicroExecution.buildRow (MicroExecution.keySource heights 0 0).1
      (MicroExecution.keySource heights start.val) (steps+1))
  have hseeds : (Vector.replicate (steps+1) (WordKey.cellWord (classSeed heights hh))).map Fin.val =
      (Vector.replicate (steps+1) (MicroExecution.keySource heights 0 0).1).map
        (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1))) := by
    simp [WordKey.cellWord,classSeed,encodeKey]
  rw [hseeds] at ht
  have hsource : (fun start : Fin (steps+1) => transport (Vector.map Fin.val)
      (wordRow (classSeed heights hh) (MicroExecution.keySource heights start.val)
        (steps+1) (steps+1) le_rfl (fun i hi => heightSource_fits heights hh start.val i start.isLt hi))) =
      fun start : Fin (steps+1) => transport
        (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1))))
        (MicroExecution.buildRow (MicroExecution.keySource heights 0 0).1
          (MicroExecution.keySource heights start.val) (steps+1)) := by
    funext start
    exact hw start
  rw [hsource,he] at ht
  have hv := congrArg Prod.fst ht
  have hc := congrArg Prod.snd ht
  apply Prod.ext
  · exact hv.symm
  · simp only [transport] at hc ⊢
    omega

def canonicalRun (steps code : Nat) : Measured {h : Heights steps // HeightDomain steps h} Nat :=
  let r := MicroExecution.canonicalM steps code
  (⟨r.1,by rw [MicroExecution.canonicalM_value]; exact canonical_bounds steps code⟩,r.2)

def sharedZero (steps : Nat) : Cell (steps : Int) (2*steps+1) (2*(steps+1)) :=
  ⟨toLex (0,0),by simp only [ofLex_toLex,Int.zero_add]; exact ⟨by omega,by omega,by omega⟩⟩

def sharedProgram (steps : Nat) :=
  bind (TableExecution.initStore (WordKey.cellWord (sharedZero steps)) (steps+1)) fun seedRow =>
  bind (TableExecution.initStore seedRow (steps+1)) fun seedClass =>
  TableExecution.tabulate seedClass (fun code : Fin (2^steps) =>
    bind (canonicalRun steps code.val) fun heights => classProgram heights.val heights.property)

theorem sharedProgram_refines (steps : Nat) :
    transport (Vector.map (Vector.map (Vector.map Fin.val))) (sharedProgram steps) =
      transport (Vector.map (Vector.map (Vector.map
        (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1)))))) (MicroExecution.sharedM steps) := by
  have hc : ∀ code : Fin (2^steps),
      transport (Vector.map (Vector.map Fin.val))
        (bind (canonicalRun steps code.val) fun heights => classProgram heights.val heights.property) =
      transport (Vector.map (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1)))))
        (bind (MicroExecution.canonicalM steps code.val) fun heights => MicroExecution.buildClassM heights) := by
    intro code
    have hh := classProgram_refines (canonicalRun steps code.val).1.val (canonicalRun steps code.val).1.property
    have hv := congrArg Prod.fst hh
    have hw := congrArg Prod.snd hh
    apply Prod.ext
    · exact hv
    · simp only [Resources.bind,transport,canonicalRun] at hw ⊢
      omega
  have ht := tabulate_transport (Vector.map (Vector.map Fin.val))
    (Vector.replicate (steps+1) (Vector.replicate (steps+1) (WordKey.cellWord (sharedZero steps))))
    (fun code : Fin (2^steps) => bind (canonicalRun steps code.val) fun heights => classProgram heights.val heights.property)
  have he := tabulate_transport
    (Vector.map (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1)))))
    (Vector.replicate (steps+1) (Vector.replicate (steps+1) (toLex ((0 : Int),(0 : Nat)))))
    (fun code : Fin (2^steps) => bind (MicroExecution.canonicalM steps code.val) fun heights => MicroExecution.buildClassM heights)
  have hseed :
      (Vector.replicate (steps+1) (Vector.replicate (steps+1) (WordKey.cellWord (sharedZero steps)))).map
        (Vector.map Fin.val) =
      (Vector.replicate (steps+1) (Vector.replicate (steps+1) (toLex ((0 : Int),(0 : Nat))))).map
        (Vector.map (encodeKey (offset := (steps : Int)) (stride := 2*(steps+1)))) := by
    simp [WordKey.cellWord,sharedZero,encodeKey]
  rw [hseed,funext hc,he] at ht
  have hv := congrArg Prod.fst ht
  have hw := congrArg Prod.snd ht
  simp only [sharedProgram,MicroExecution.sharedM,Resources.bind,TableExecution.initStore_exact]
  apply Prod.ext
  · exact hv.symm
  · simp only [transport,Resources.bind] at hw ⊢
    omega

open PreparationBounds PackedBackend TreeReduction

def macroSeed (input : Input m) : Cell 0 (2*m) (paddedCapacity m) :=
  ⟨toLex (0,0),by
    have hp := paddedCapacity_covers input.positive
    have hn := input.positive
    simp only [ofLex_toLex,Int.add_zero]
    exact ⟨by omega,by omega,by omega⟩⟩

theorem macroMinima_fits (input : Input m) (i : Fin (blocks m)) :
    Fits 0 (2*m) (paddedCapacity m)
      (BlockedRMQ.blockMinima (state input).micro (blocks_pos m))[i.val] := by
  rw [state_eq]
  have hh := paddedBlockMinima_fits (fun j => (input.depth j : Int)) input.positive (blocks_pos m)
    (Backend.input_steps input) (depth_bounds input) (padded_le input) i
  simpa only [dimension,paddedCapacity,BlockedRMQ.buildPadded,BlockedRMQ.build,blocks] using hh

def macroProgram (input : Input m) :=
  wordSparse (macroSeed input) (BlockedRMQ.blockMinima (state input).micro (blocks_pos m))
    (macroMinima_fits input) (levels m)

theorem macroProgram_refines (input : Input m) :
    transport (fun pair => (rowsMap Fin.val pair.1,pair.2)) (macroProgram input) =
      transport (fun pair =>
        (rowsMap (encodeKey (offset := 0) (stride := paddedCapacity m)) pair.1,pair.2))
        (SparseExecution.prepare (toLex ((0 : Int),(0 : Nat)))
          (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)) :=
  wordSparse_refines _ _ _ _

/-- The finite-cell program and the existing arena/control interpretations
share the same sparse execution value; storage observations are taken from
those independent executable interpretations, not attached to the result. -/
theorem macroProgram_workspace_alignment (input : Input m) :
    transport (fun pair => (rowsMap Fin.val pair.1,pair.2)) (macroProgram input) =
      ( (rowsMap (encodeKey (offset := 0) (stride := paddedCapacity m))
          (Workspace.sparseRun (toLex ((0 : Int),(0 : Nat)))
            (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).value.1,
          (Workspace.sparseRun (toLex ((0 : Int),(0 : Nat)))
            (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).value.2),
        (SparseExecution.prepare (toLex ((0 : Int),(0 : Nat)))
          (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).2) := by
  rw [macroProgram_refines,Workspace.sparseRun_value]
  rfl

theorem macroProgram_control_alignment (input : Input m) :
    transport (fun pair => (rowsMap Fin.val pair.1,pair.2)) (macroProgram input) =
      ( (rowsMap (encodeKey (offset := 0) (stride := paddedCapacity m))
          (Control.sparseRun (toLex ((0 : Int),(0 : Nat)))
            (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).value.1,
          (Control.sparseRun (toLex ((0 : Int),(0 : Nat)))
            (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).value.2),
        (SparseExecution.prepare (toLex ((0 : Int),(0 : Nat)))
          (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).2) := by
  rw [macroProgram_refines,Control.sparseRun_value]
  rfl

theorem sharedProgram_cost (steps : Nat) :
    (sharedProgram steps).2 = (MicroExecution.sharedM steps).2 :=
  congrArg Prod.snd (sharedProgram_refines steps)

theorem sharedProgram_payload (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    (((sharedProgram (blockSize m-1)).1[code.val][start.val][len.val]).val) =
      ((sharedWords input h)[2^(blockSize m-1)+
        code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
        ((blockSize m-1+1)+start.val*(blockSize m-1+1)+len.val)]'
        (FlatTable.payload_index_lt code ⟨_,FlatTable.payload_index_lt start len⟩)).val := by
  rw [sharedWords_read,prepared_shared]
  have hh := congrArg (fun r => r.1[code.val][start.val][len.val])
    (sharedProgram_refines (blockSize m-1))
  simp only [transport,Vector.getElem_map,MicroExecution.sharedM_value,encodeKey] at hh
  exact hh

theorem sharedProgram_index (steps : Nat) (code : Fin (2^steps)) (start len : Fin (steps+1)) :
    ((sharedProgram steps).1[code.val][start.val][len.val]).val % (2*(steps+1)) =
      lookupShared (prepareShared steps) code start len := by
  have hh := congrArg (fun r => r.1[code.val][start.val][len.val]) (sharedProgram_refines steps)
  simp only [transport,Vector.getElem_map,MicroExecution.sharedM_value,encodeKey] at hh
  rw [hh]
  unfold WordKey.encode
  have hf : (ofLex (prepareShared steps)[code.val][start.val][len.val]).2 < 2*(steps+1) :=
    (sharedCell_fits code start len).2.2
  exact WordKey.pack_mod hf

theorem macro_rows (input : Input m) :
    (SparseExecution.prepare (toLex ((0 : Int),(0 : Nat)))
      (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (levels m)).1.1 =
      (state input).macroRows := by
  rw [state_eq]
  rfl

theorem macroProgram_payload (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (((macroProgram input).1.1[level.val]).1[i.val]).val =
      ((macroPack input h)[(levels m+1)+level.val*blocks m+i.val]'
        (FlatTable.payload_index_lt level i)).val := by
  rw [macroPack_read]
  have hh := congrArg (fun r => (r.1.1[level.val]).1[i.val]) (macroProgram_refines input)
  simp only [transport,rowsMap,Vector.getElem_map,encodeKey,macro_rows] at hh
  simpa only [dimension,paddedCapacity] using hh

/-- Domain widening is a representation map into the selected physical word
width. It is not an extra traversal charged to initialization. -/
def widen (h : product ≤ 2^width) (word : Fin product) : WordMachine.Word width :=
  ⟨word.val,word.isLt.trans_le h⟩

theorem sharedProgram_width (input : Input m)
    (h : MachineCapacity.WordEligible m width capacity)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    ((sharedProgram (blockSize m-1)).1[code.val][start.val][len.val]).val < 2^width :=
  Fin.isLt _ |>.trans_le (micro_width input h)

theorem macroProgram_width (input : Input m)
    (h : MachineCapacity.WordEligible m width capacity)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    (((macroProgram input).1.1[level.val]).1[i.val]).val < 2^width :=
  Fin.isLt _ |>.trans_le ((KeyBounds.macro_capacity_le (paddedCapacity_le input.positive)).trans h.keys)

theorem sharedProgram_physical (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    widen (micro_width input h.toWordEligible)
      ((sharedProgram (blockSize m-1)).1[code.val][start.val][len.val]) =
      (sharedWords input h)[2^(blockSize m-1)+
        code.val*FlatTable.words (blockSize m-1+1) (blockSize m-1+1)+
        ((blockSize m-1+1)+start.val*(blockSize m-1+1)+len.val)]'
        (FlatTable.payload_index_lt code ⟨_,FlatTable.payload_index_lt start len⟩) := by
  apply Fin.ext
  exact sharedProgram_payload input h code start len

theorem macroProgram_physical (input : Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (level : Fin (levels m+1)) (i : Fin (blocks m)) :
    widen ((KeyBounds.macro_capacity_le (paddedCapacity_le input.positive)).trans h.keys)
      (((macroProgram input).1.1[level.val]).1[i.val]) =
      (macroPack input h)[(levels m+1)+level.val*blocks m+i.val]'
        (FlatTable.payload_index_lt level i) := by
  apply Fin.ext
  exact macroProgram_payload input h level i

/-- A key source charges address addition, clipping and a depth load, followed
by the two arithmetic steps of radix packing. Canonical signed depth plus its
offset is represented by a stored nonnegative height; this representation map
is proof-side, not an uncharged online arithmetic instruction. -/
theorem micro_source_tariff (steps code start i : Nat) :
    (MicroExecution.keySource (canonicalHeights steps code) start i).2 = 5 := by
  rw [MicroExecution.keySource_exact]

theorem micro_packing_intermediates (input : Input m)
    (h : MachineCapacity.WordEligible m width capacity)
    (code start i : Nat) (hs : start < blockSize m-1+1) (hi : i < blockSize m-1+1) :
    let cell : Cell ((blockSize m-1 : Nat) : Int) (2*(blockSize m-1)+1) (2*(blockSize m-1+1)) :=
      ⟨(MicroExecution.keySource (canonicalHeights (blockSize m-1) code) start i).1,
        PreparationInvariants.keySource_fits _ _ _ _ hs hi⟩
    ((ofLex cell.val).1+(blockSize m-1 : Nat)).toNat * (2*(blockSize m-1+1)) < 2^width ∧
      (ofLex cell.val).2 < 2^width ∧ (WordKey.cellWord cell).val < 2^width :=
  WordKey.packing_intermediates _ (micro_width input h)

theorem widen_min (h : product ≤ 2^width) (a b : Fin product) :
    widen h (min a b) = min (widen h a) (widen h b) := by
  apply Fin.ext
  simp [widen,Fin.val_min]

/-- Changing from the proven radix capacity to the physical word width
commutes with the whole executed row, preserving every operation count. -/
theorem physical_row (h : product ≤ 2^width) (seed : Fin product)
    (source : Nat → Measured (Fin product) Nat) (capacity len : Nat) (hl : len ≤ capacity) :
    MicroExecution.rowFill (widen h seed) (fun i => transport (widen h) (source i)) capacity len hl =
      transport (Vector.map (widen h)) (MicroExecution.rowFill seed source capacity len hl) :=
  rowFill_transport (widen h) (widen_min h) seed source capacity len hl

def wideMacroProgram (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :=
  let bound := (KeyBounds.macro_capacity_le (paddedCapacity_le input.positive)).trans h.keys
  SparseExecution.prepare (widen bound (WordKey.cellWord (macroSeed input)))
    ((WordKey.encodeStore (liftVector
      (BlockedRMQ.blockMinima (state input).micro (blocks_pos m)) (macroMinima_fits input))).map (widen bound))
    (levels m)

theorem wideMacroProgram_refines (input : Input m) (h : MachineCapacity.WordEligible m width capacity) :
    wideMacroProgram input h =
      transport (fun pair => (rowsMap
        (widen ((KeyBounds.macro_capacity_le (paddedCapacity_le input.positive)).trans h.keys)) pair.1,pair.2))
        (macroProgram input) :=
  sparsePrepare_transport _ (widen_min _) _ _ _

example : ((sharedProgram 1).1[0][0][1]).val = 1 := by decide
example : ((sharedProgram 1).1[0][0][1]).val % 4 = 1 := by decide

end Sequences.LCA.PreparationCertificate
