import Applications.Sequences.LCA.PreparationInvariants
import Applications.Sequences.LCA.TableTransport
import Applications.Sequences.LCA.PackedBackend
import Applications.Sequences.LCA.Control

/-! Executed finite-cell preparation refines the raw key programs. Source
lifting defaults only outside the visited prefix; both output and primitive
cost are transported through every initialized and updated row. -/
namespace Sequences.LCA.PreparationCertificate
open Resources Dijkstra.Store KeyBounds TableTransport
abbrev Cell := WordKey.Cell

variable {offset : Int} {heights stride n : Nat}

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

end Sequences.LCA.PreparationCertificate
