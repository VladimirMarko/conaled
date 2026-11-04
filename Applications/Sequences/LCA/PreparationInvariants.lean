import Applications.Sequences.LCA.KeyBounds
import Applications.Sequences.LCA.MicroExecution

/-! Key domains for the executed partial row builder, including initialized
slots that have not yet been filled. -/
namespace Sequences.LCA.PreparationInvariants
open Dijkstra.Store Resources PreparedRMQ KeyBounds

variable {α : Type} [LinearOrder α]

theorem rowFill_unfilled (seed : α) (source : Nat → Measured α Nat) (capacity len : Nat)
    (h : len ≤ capacity) (j : Fin capacity) (hj : len ≤ j.val) :
    lookup (MicroExecution.rowFill seed source capacity len h).1 j = seed := by
  induction len with
  | zero => simp [MicroExecution.rowFill,TableExecution.initStore_exact,lookup]
  | succ k ih =>
    have he : (⟨k,by omega⟩ : Fin capacity) ≠ j := by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_mk] at hh; omega
    dsimp only [MicroExecution.rowFill,MicroExecution.rowIndex,Resources.bind,
      TableExecution.store,TableExecution.read,MicroExecution.minimum]
    split <;> rw [lookup_write,if_neg he] <;> exact ih (by omega) (by omega)

theorem rowFill_fits (seed : Key) (source : Nat → Measured Key Nat) (capacity len : Nat)
    (h : len ≤ capacity) (hseed : Fits offset heights stride seed)
    (hsource : ∀ i, i < len → Fits offset heights stride (source i).1) (j : Fin capacity) :
    Fits offset heights stride (lookup (MicroExecution.rowFill seed source capacity len h).1 j) := by
  by_cases hj : j.val < len
  · rw [MicroExecution.rowFill_lookup seed source capacity len h j hj]
    apply rangeMin_fits
    intro i hi
    simpa only [Nat.zero_add] using hsource i (by omega)
  · rw [rowFill_unfilled seed source capacity len h j (by omega)]
    exact hseed

example (seed : Key) (source : Nat → Measured Key Nat) (hs : Fits offset heights stride seed) :
    Fits offset heights stride (lookup (MicroExecution.rowFill seed source 2 0 (by decide)).1 1) :=
  rowFill_fits seed source 2 0 (by decide) hs (by intro i hi; omega) 1

theorem keySource_fits (steps code : Nat) (start i : Nat)
    (hs : start < steps+1) (hi : i < steps+1) :
    Fits (steps : Int) (2*steps+1) (2*(steps+1))
      (MicroExecution.keySource (canonicalHeights steps code) start i).1 := by
  rw [MicroExecution.keySource_exact]
  have hd := canonical_bounds steps code (start+i)
  simp only [Fits,depthKey,ofLex_toLex]
  exact ⟨by omega,by omega,by omega⟩

theorem microRowFill_fits (steps code : Nat) (start : Fin (steps+1)) (len : Nat)
    (hlen : len ≤ steps+1) (j : Fin (steps+1)) :
    Fits (steps : Int) (2*steps+1) (2*(steps+1))
      (lookup (MicroExecution.rowFill
        (MicroExecution.keySource (canonicalHeights steps code) 0 0).1
        (MicroExecution.keySource (canonicalHeights steps code) start.val)
        (steps+1) len hlen).1 j) := by
  apply rowFill_fits
  · exact keySource_fits steps code 0 0 (by omega) (by omega)
  · intro i hi
    exact keySource_fits steps code start.val i start.isLt (by omega)

theorem rowCell_fits (row : Vector Key n) (span : Nat) (i : Fin n)
    (hrow : ∀ j : Fin n, Fits offset heights stride row[j.val]) :
    Fits offset heights stride (SparseExecution.rowCell row span i).1 := by
  rw [SparseExecution.rowCell_value]
  exact fits_min (hrow i) (hrow ⟨(i.val+span)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem finiteRow_cell_fits (input : Vector Key n)
    (hinput : ∀ i : Fin n, Fits offset heights stride input[i.val])
    (level span : Nat) (i : Fin n) :
    Fits offset heights stride (SparseExecution.rowCell (finiteRow input level) span i).1 :=
  rowCell_fits _ span i (finiteRow_fits input hinput level)

theorem relativeCodeM_bounds (steps code i : Nat) (hi : i ≤ steps) :
    -(steps : Int) ≤ (MicroExecution.relativeCodeM code i).1 ∧
      (MicroExecution.relativeCodeM code i).1 ≤ (steps : Int) := by
  rw [MicroExecution.relativeCodeM_value steps code i hi]
  have hh := relative_bounds (decodeShape steps code) i
  have hm := Nat.min_le_right i steps
  omega

theorem codeM_lt (source : Nat → Measured Int Nat) (offset steps : Nat) :
    (MicroExecution.codeM source offset steps).1 < 2^steps := by
  rw [MicroExecution.codeM_value]
  exact shapeCode_lt _

end Sequences.LCA.PreparationInvariants
