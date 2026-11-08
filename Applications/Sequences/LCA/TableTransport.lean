import Applications.Sequences.LCA.MicroExecution
import Applications.Sequences.LCA.SparseExecution
import Applications.Sequences.LCA.WordKeyStorage

/-! Whole measured table programs commute with a minimum-preserving cell
interpretation. Equality includes cost, not only the final array contents. -/
namespace Sequences.LCA.TableTransport
open Resources Dijkstra.Store TableExecution
variable {α β : Type}

def transport (f : α → β) (r : Measured α Nat) : Measured β Nat := (f r.1,r.2)

theorem fill_transport (f : α → β) (source : Fin n → Measured α Nat)
    (indices : List (Fin n)) (mem : Store n α) :
    fill (fun i => transport f (source i)) indices (mem.map f) =
      transport (Vector.map f) (fill source indices mem) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i rest ih =>
    simp only [fill, Resources.bind, visitIndex, store, transport]
    simp only [write, ← Vector.map_set]
    have hh := ih (mem.set i.val (source i).1)
    simpa [transport] using congrArg (fun r => (r.1,2+((source i).2+(1+r.2)))) hh

theorem tabulate_transport (f : α → β) (seed : α) (source : Fin n → Measured α Nat) :
    tabulate (f seed) (fun i => transport f (source i)) =
      transport (Vector.map f) (tabulate seed source) := by
  simp only [tabulate, initStore_exact, Resources.bind]
  have hh := fill_transport f source (List.finRange n) (Vector.replicate n seed)
  simpa [transport] using congrArg (fun r => (r.1,3*n+r.2)) hh

variable [LinearOrder α] [LinearOrder β]

theorem rowFill_transport (f : α → β) (hf : ∀ a b, f (min a b) = min (f a) (f b))
    (seed : α) (source : Nat → Measured α Nat) (capacity len : Nat) (h : len ≤ capacity) :
    MicroExecution.rowFill (f seed) (fun i => transport f (source i)) capacity len h =
      transport (Vector.map f) (MicroExecution.rowFill seed source capacity len h) := by
  induction len with
  | zero => simp [MicroExecution.rowFill, initStore_exact, transport]
  | succ k ih =>
    simp only [MicroExecution.rowFill]
    rw [ih]
    simp only [Resources.bind, MicroExecution.rowIndex,
      transport, store, TableExecution.read, MicroExecution.minimum]
    by_cases hk : k = 0
    · simp [hk, write, Vector.map_set]
    · simp [hk, lookup, write, Vector.map_set, hf]

/-- A bounded row never observes source positions outside its initialized
prefix. This lets a finite-cell lifting totalize its unused source positions. -/
theorem rowFill_congr_source (seed : α) (source other : Nat → Measured α Nat)
    (capacity len : Nat) (h : len ≤ capacity)
    (he : ∀ i, i < len → source i = other i) :
    MicroExecution.rowFill seed source capacity len h =
      MicroExecution.rowFill seed other capacity len h := by
  induction len with
  | zero => rfl
  | succ k ih =>
    simp only [MicroExecution.rowFill]
    rw [ih (by omega) (by intro i hi; exact he i (by omega))]
    simp only [Resources.bind, MicroExecution.rowIndex, he k (by omega)]
    rfl

theorem buildRow_transport (f : α → β) (hf : ∀ a b, f (min a b) = min (f a) (f b))
    (seed : α) (source : Nat → Measured α Nat) (n : Nat) :
    MicroExecution.buildRow (f seed) (fun i => transport f (source i)) n =
      transport (Vector.map f) (MicroExecution.buildRow seed source n) :=
  rowFill_transport f hf seed source n n le_rfl

theorem rowCell_transport (f : α → β) (hf : ∀ a b, f (min a b) = min (f a) (f b))
    (row : Vector α n) (span : Nat) (i : Fin n) :
    SparseExecution.rowCell (row.map f) span i = transport f (SparseExecution.rowCell row span i) := by
  simp [SparseExecution.rowCell, transport, Resources.bind, TableExecution.read, lookup, hf]

theorem nextRow_transport (f : α → β) (hf : ∀ a b, f (min a b) = min (f a) (f b))
    (seed : α) (row : Vector α n) (span : Nat) :
    SparseExecution.nextRow (f seed) (row.map f) span =
      transport (Vector.map f) (SparseExecution.nextRow seed row span) := by
  unfold SparseExecution.nextRow
  have he : SparseExecution.rowCell (row.map f) span =
      fun i => transport f (SparseExecution.rowCell row span i) :=
    funext (rowCell_transport f hf row span)
  rw [he]
  exact tabulate_transport f seed _

def rowsMap (f : α → β) (rows : Vector (Vector α n × Nat) k) : Vector (Vector β n × Nat) k :=
  rows.map fun row => (row.1.map f,row.2)

theorem sparseBuild_transport (f : α → β) (hf : ∀ a b, f (min a b) = min (f a) (f b))
    (seed : α) (input : Vector α n) (levels : Nat) :
    SparseExecution.build (f seed) (input.map f) levels =
      transport (rowsMap f) (SparseExecution.build seed input levels) := by
  induction levels with
  | zero =>
    have hr : (fun i => read (input.map f) i) = fun i => transport f (read input i) := by
      funext i
      simp [TableExecution.read, lookup, transport]
    simp only [SparseExecution.build, hr]
    rw [tabulate_transport]
    simp [Resources.bind, transport, rowsMap]
  | succ k ih =>
    simp only [SparseExecution.build, ih, Resources.bind, transport, rowsMap, Vector.getElem_map]
    rw [nextRow_transport f hf]
    simp [transport, Vector.map_push]

theorem sparsePrepare_transport (f : α → β) (hf : ∀ a b, f (min a b) = min (f a) (f b))
    (seed : α) (input : Vector α n) (levels : Nat) :
    SparseExecution.prepare (f seed) (input.map f) levels =
      transport (fun pair => (rowsMap f pair.1,pair.2)) (SparseExecution.prepare seed input levels) := by
  simp [SparseExecution.prepare, sparseBuild_transport f hf, transport, Resources.bind, Resources.pure]

/-- Finite-word specialization, covering every intermediate initialized row
and preserving the complete preparation's primitive-event count. -/
theorem wordSparsePrepare (seed : WordKey.Cell offset heights stride)
    (input : Vector (WordKey.Cell offset heights stride) n) (levels : Nat) :
    SparseExecution.prepare (WordKey.cellWord seed) (WordKey.encodeStore input) levels =
      transport (fun pair => (rowsMap WordKey.cellWord pair.1,pair.2))
        (SparseExecution.prepare seed input levels) :=
  sparsePrepare_transport WordKey.cellWord WordKey.cellWord_min seed input levels

theorem wordBuildRow (seed : WordKey.Cell offset heights stride)
    (source : Nat → Measured (WordKey.Cell offset heights stride) Nat) (n : Nat) :
    MicroExecution.buildRow (WordKey.cellWord seed) (fun i => transport WordKey.cellWord (source i)) n =
      transport (Vector.map WordKey.cellWord) (MicroExecution.buildRow seed source n) :=
  buildRow_transport WordKey.cellWord WordKey.cellWord_min seed source n

private def early : WordKey.Cell 2 4 4 := ⟨toLex (-1,1),by decide⟩
private def late : WordKey.Cell 2 4 4 := ⟨toLex (-1,3),by decide⟩

/-- The encoded two-entry sparse construction performs the same 57 events as
its bounded-key source, including a comparison between equal-depth keys. -/
example :
    (SparseExecution.prepare (WordKey.cellWord early) (WordKey.encodeStore #v[late,early]) 1).2 = 57 := by
  rw [wordSparsePrepare]
  decide

example :
    (MicroExecution.buildRow (WordKey.cellWord early)
      (fun i => transport WordKey.cellWord ((if i=0 then late else early),1)) 2).2 = 18 := by
  rw [wordBuildRow]
  decide

/-- Even an expensive, unrelated tail cannot affect a bounded row run. -/
example : MicroExecution.rowFill 0
    (fun i => if i<2 then (i,1) else (999,99)) 2 2 (by decide) =
      MicroExecution.rowFill 0 (fun i => (i,1)) 2 2 (by decide) := by
  apply rowFill_congr_source
  intro i hi
  simp [hi]

end Sequences.LCA.TableTransport
