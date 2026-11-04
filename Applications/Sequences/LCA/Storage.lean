import Applications.Sequences.LCA.Arena
import Applications.Sequences.LCA.BlockedRMQ
import Applications.Sequences.LCA.PreparationBounds

/-! Storage observations of the actual nested finite arrays, and disjoint
reserved regions for preprocessing. Keys occupy one encoded word; the encoding
and width obligations are supplied by KeyBounds/WordKeyStorage. -/
namespace Sequences.LCA.Storage
open BlockedRMQ

def classWords (table : ClassTable steps) : Nat :=
  table.toArray.size + (table.toList.map (fun row => row.toArray.size)).sum

def sharedWords (table : SharedTable steps) : Nat :=
  table.toArray.size + (table.toList.map classWords).sum

def dataWords (data : Data steps blocks levels) : Nat :=
  data.micro.depths.toArray.size + data.micro.classes.toArray.size + sharedWords data.micro.shared +
  2*data.macroRows.toArray.size +
    (data.macroRows.toList.map (fun row => row.1.toArray.size)).sum + data.macroLogs.toArray.size

theorem classWords_eq (table : ClassTable steps) :
    classWords table = (steps+1)+(steps+1)*(steps+1) := by
  simp [classWords, List.sum_replicate]

theorem sharedWords_eq (table : SharedTable steps) :
    sharedWords table = 2^steps*((steps+1)*(steps+1)+(steps+1)+1) := by
  have hf : (classWords : ClassTable steps → Nat) = fun _ => (steps+1)+(steps+1)*(steps+1) := funext classWords_eq
  simp [sharedWords, hf, List.sum_replicate]
  ring

theorem dataWords_eq (data : Data steps blocks levels) :
    dataWords data = blocks*(steps+1)+blocks+
      2^steps*((steps+1)*(steps+1)+(steps+1)+1)+
      SparseExecution.retainedSlots blocks levels := by
  simp only [dataWords, Vector.size_toArray, sharedWords_eq]
  simp [List.sum_replicate, SparseExecution.retainedSlots]
  ring

theorem dataWords_le (_hn : 0 < n)
    (data : Data (blockSize n-1) (PreparationBounds.blocks n) (PreparationBounds.levels n)) :
    dataWords data ≤ PreparationBounds.retainedSlots n := by
  rw [dataWords_eq]
  have hb := blockSize_pos n
  have he : blockSize n-1+1 = blockSize n := by omega
  simp only [he]
  unfold PreparationBounds.retainedSlots PreparationBounds.paddedCapacity PreparationBounds.sharedSlots
  omega

/-- Each region is reserved once. The block-minimum region is retained until
preparation ends; no early reclamation is needed for the bound. -/
inductive Region where
  | depths | classes | shared | minima | sparse | workspace | input
  deriving DecidableEq, Repr

def regionSize (n inputWords : Nat) : Region → Nat
  | .depths => PreparationBounds.paddedCapacity n
  | .classes => PreparationBounds.blocks n
  | .shared => PreparationBounds.sharedSlots n
  | .minima => PreparationBounds.blocks n
  | .sparse => SparseExecution.retainedSlots (PreparationBounds.blocks n) (PreparationBounds.levels n)
  | .workspace => PreparationBounds.workspaceSlots n
  | .input => inputWords

def regionBase (n inputWords : Nat) : Region → Nat
  | .depths => 0
  | .classes => regionSize n inputWords .depths
  | .shared => regionSize n inputWords .depths + regionSize n inputWords .classes
  | .minima => regionSize n inputWords .depths + regionSize n inputWords .classes + regionSize n inputWords .shared
  | .sparse => regionSize n inputWords .depths + regionSize n inputWords .classes + regionSize n inputWords .shared + regionSize n inputWords .minima
  | .workspace => regionSize n inputWords .depths + regionSize n inputWords .classes + regionSize n inputWords .shared + regionSize n inputWords .minima + regionSize n inputWords .sparse
  | .input => regionSize n inputWords .depths + regionSize n inputWords .classes + regionSize n inputWords .shared + regionSize n inputWords .minima + regionSize n inputWords .sparse + regionSize n inputWords .workspace

def address (n inputWords : Nat) (r : Region) (i : Fin (regionSize n inputWords r)) : Nat :=
  regionBase n inputWords r + i.val

theorem region_end_le (n inputWords : Nat) (r : Region) :
    regionBase n inputWords r + regionSize n inputWords r ≤ PreparationBounds.peakSlots n inputWords := by
  cases r <;> simp [regionBase, regionSize, PreparationBounds.peakSlots, PreparationBounds.retainedSlots] <;> omega

theorem address_lt (n inputWords : Nat) (r : Region) (i : Fin (regionSize n inputWords r)) :
    address n inputWords r i < PreparationBounds.peakSlots n inputWords := by
  have h := region_end_le n inputWords r
  have hi := i.isLt
  unfold address
  omega

theorem address_injective_region (n inputWords : Nat) (r : Region) :
    Function.Injective (address n inputWords r) := by
  intro i j h
  apply Fin.ext
  unfold address at h
  omega

theorem different_regions_disjoint (n inputWords : Nat) (r s : Region) (h : r ≠ s)
    (i : Fin (regionSize n inputWords r)) (j : Fin (regionSize n inputWords s)) :
    address n inputWords r i ≠ address n inputWords s j := by
  have hi := i.isLt
  have hj := j.isLt
  cases r <;> cases s <;> simp_all [address, regionBase, regionSize] <;> omega

def segment (n inputWords : Nat) (r : Region) :
    Arena.Segment (PreparationBounds.peakSlots n inputWords) (regionSize n inputWords r) :=
  ⟨regionBase n inputWords r, region_end_le n inputWords r⟩

theorem segments_disjoint (n inputWords : Nat) (r s : Region) (h : r ≠ s) :
    Arena.Disjoint (segment n inputWords r) (segment n inputWords s) := by
  cases r <;> cases s <;>
    simp_all [Arena.Disjoint, segment, regionBase, regionSize] <;> omega

/-- A region is an actual finite vector of words, installed into a finite
initialized flat arena. Its reads and later writes use `Arena`'s simulation. -/
def realizeRegion (n inputWords width : Nat) (r : Region)
    (cells : Dijkstra.Store.Store (regionSize n inputWords r) (Fin (2^width))) :=
  Arena.install (segment n inputWords r) cells
    (Arena.initialized (PreparationBounds.peakSlots n inputWords) width)

theorem realizeRegion_reads (n inputWords width : Nat) (r : Region)
    (cells : Dijkstra.Store.Store (regionSize n inputWords r) (Fin (2^width))) :
    Arena.Represents (segment n inputWords r) cells (realizeRegion n inputWords width r cells) :=
  Arena.install_represents _ _ _

example : regionBase 3 6 .classes = 3 := by decide
example : regionBase 3 6 .minima = 9 := by decide
example : Arena.Disjoint (segment 3 6 .depths) (segment 3 6 .classes) :=
  segments_disjoint 3 6 _ _ (by decide)

end Sequences.LCA.Storage
