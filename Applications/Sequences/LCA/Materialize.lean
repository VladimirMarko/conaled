import Applications.Sequences.LCA.WordMachine
import Applications.Sequences.LCA.Control

namespace Sequences.LCA.Materialize
open Resources Dijkstra.Store WordMachine

/-- A resident-buffer view. Joining views allocates no concatenated array. -/
inductive Chunks (width : Nat)
  | leaf {n : Nat} (cells : Vector (Word width) n)
  | zero (n : Nat)
  | join (left right : Chunks width)

def Chunks.size : Chunks width → Nat
  | .leaf (n := n) _ => n
  | .zero n => n
  | .join a b => a.size+b.size

def Chunks.depth : Chunks width → Nat
  | .leaf _ => 0
  | .zero _ => 0
  | .join a b => max a.depth b.depth+1

def Chunks.flatten : (c : Chunks width) → Vector (Word width) c.size
  | .leaf cells => cells
  | .zero n => Vector.replicate n (word width 0)
  | .join a b => a.flatten ++ b.flatten

def indexM (value bound : Nat) (hv : value < bound) (hw : value < 2^width) :
    Measured (Fin bound) Nat :=
  let r := scalar width value
  (⟨r.1.val,by change (scalar width value).1.val < bound; simpa only [scalar,word_of_lt hw] using hv⟩,r.2)

theorem indexM_exact (value bound : Nat) (hv : value < bound) (hw : value < 2^width) :
    indexM (width := width) value bound hv hw = (⟨value,hv⟩,1) := by
  apply Prod.ext
  · apply Fin.ext; exact word_of_lt hw
  · rfl

def Chunks.read : (c : Chunks width) → c.size ≤ 2^width → Fin c.size → Measured (Word width) Nat
  | .leaf cells, _, i => TableExecution.read cells i
  | .zero _, _, _ => pure (word width 0)
  | .join a b, hw, i =>
    let run := if hi : i.val<a.size then a.read (by simp only [size] at hw; omega) ⟨i.val,hi⟩ else
      bind (indexM (width := width) (i.val-a.size) b.size (by have := i.isLt; simp only [size] at this; omega)
        (by have := i.isLt; simp only [size] at this hw; omega)) fun j =>
          b.read (by simp only [size] at hw; omega) j
    (run.1,run.2+1)

theorem Chunks.read_value (c : Chunks width) (hw : c.size ≤ 2^width) (i : Fin c.size) :
    (c.read hw i).1 = c.flatten[i.val] := by
  induction c with
  | leaf cells => rfl
  | zero n => simp [read,flatten,size,Resources.pure]
  | join a b ia ib =>
    simp only [read,flatten,size]
    split
    · simp only [ia,Vector.getElem_append]; simp_all
    · simp only [indexM_exact,Resources.bind,ib,Vector.getElem_append]; simp_all

theorem Chunks.read_cost (c : Chunks width) (hw : c.size ≤ 2^width) (i : Fin c.size) :
    (c.read hw i).2 ≤ 2*c.depth+1 := by
  induction c with
  | leaf cells => simp [read,depth,TableExecution.read]
  | zero n => simp [read,depth,Resources.pure]
  | join a b ia ib =>
    have ha := Nat.le_max_left a.depth b.depth
    have hb := Nat.le_max_right a.depth b.depth
    simp only [read,depth]
    split
    · have hh := ia (by simp only [size] at hw; omega) ⟨i.val,by assumption⟩; omega
    · simp only [indexM_exact,Resources.bind]
      have hh := ib (by simp only [size] at hw; omega)
        ⟨i.val-a.size,by have := i.isLt; simp only [size] at this; omega⟩
      omega

def cell (c : Chunks width) (hw : c.size ≤ 2^width) (i : Nat) : Measured (Word width) Nat :=
  let run := if hi : i<c.size then c.read hw ⟨i,hi⟩ else pure (word width 0)
  (run.1,run.2+1)

def run (c : Chunks width) (hw : c.size ≤ 2^width) (capacity : Nat) :=
  TableExecution.tabulate (word width 0) (fun i : Fin capacity => cell c hw i.val)

theorem run_read (c : Chunks width) (hw : c.size ≤ 2^width) (capacity : Nat) (i : Fin capacity) :
    lookup (run c hw capacity).1 i =
      if hi : i.val<c.size then c.flatten[i.val] else word width 0 := by
  rw [run,TableExecution.tabulate_lookup]
  simp only [cell]
  split <;> simp_all [Chunks.read_value,Resources.pure]

theorem run_cost (c : Chunks width) (hw : c.size ≤ 2^width) (capacity : Nat) :
    (run c hw capacity).2 ≤ capacity*(2*c.depth+8) := by
  apply TableExecution.tabulate_cost
  intro i
  simp only [cell]
  split
  · have hh := c.read_cost hw ⟨i.val,by assumption⟩; omega
  · simp [Resources.pure]

example : (run (.join (.leaf #v[word 8 7,word 8 9]) (.zero 1)) (by decide) 5).1 =
    #v[word 8 7,word 8 9,word 8 0,word 8 0,word 8 0] := by decide

end Sequences.LCA.Materialize

namespace Sequences.LCA.Materialize
open Dijkstra.Store PackedBackend PreparationBounds WordMachine

def chunks (r : Representation m width) : Chunks width :=
  .join (.join (.join (.join (.join (.join (.leaf r.depths) (.leaf r.classes))
    (.leaf r.shared)) (.zero (blocks m))) (.leaf r.macroTable)) (.leaf r.spans)) (.leaf r.logs)

theorem chunks_size (r : Representation m width) : (chunks r).size = retainedSlots m := by
  simp only [chunks,Chunks.size]
  rw [FlatTable.sharedPack_size,dimension]
  unfold retainedSlots paddedCapacity sharedSlots SparseExecution.retainedSlots FlatTable.words
  ring

theorem chunks_flatten (r : Representation m width) :
    (chunks r).flatten.cast (chunks_size r) = r.flatten := by
  have hz : word width 0 = (⟨0,Nat.two_pow_pos width⟩ : Word width) := by
    apply Fin.ext
    simp [word]
  simp only [chunks,Chunks.flatten,Representation.flatten,hz]
  rfl

theorem chunks_depth (r : Representation m width) : (chunks r).depth = 6 := rfl

def install (r : Representation m width) (hw : retainedSlots m ≤ 2^width) (capacity : Nat) :=
  run (chunks r) (by rw [chunks_size]; exact hw) capacity

theorem install_value (r : Representation m width) (hw : retainedSlots m ≤ 2^width)
    (capacity : Nat) (fit : retainedSlots m ≤ capacity) :
    (install r hw capacity).1 = Arena.install (⟨0,by omega⟩ : Arena.Segment capacity (retainedSlots m))
      r.flatten (Arena.initialized capacity width) := by
  apply Vector.ext
  intro i hi
  have hh := run_read (chunks r) (by rw [chunks_size]; exact hw) capacity ⟨i,hi⟩
  have he := chunks_flatten r
  have hv : (chunks r).flatten = r.flatten.cast (chunks_size r).symm := by
    rw [← he]
    simp
  change lookup (install r hw capacity).1 ⟨i,hi⟩ = _
  rw [install,hh]
  simp only [chunks_size] at *
  simp only [Arena.install,Vector.getElem_ofFn,Arena.initialized,lookup]
  split_ifs <;> try omega
  all_goals simp_all [Vector.getElem_cast,word]

theorem install_cost (r : Representation m width) (hw : retainedSlots m ≤ 2^width) (capacity : Nat) :
    (install r hw capacity).2 ≤ 20*capacity := by
  have hh := run_cost (chunks r) (by rw [chunks_size]; exact hw) capacity
  simpa [install,chunks_depth,Nat.mul_comm] using hh

end Sequences.LCA.Materialize

namespace Sequences.LCA.Materialize
open Dijkstra.Store WordMachine

def Chunks.observe : (c : Chunks width) → c.size ≤ 2^width → Fin c.size → Control.Run (Word width)
  | .leaf cells, _, i => Control.note (lookup cells i) [.ref cells,.nat i.val,.ref (lookup cells i)]
  | .zero _, _, _ => Control.note (word width 0) [.ref (word width 0)]
  | .join a b, hw, i =>
    if hi : i.val<a.size then
      Control.scope [.ref a,.ref b,.nat i.val,.bit true]
        (a.observe (by simp only [size] at hw; omega) ⟨i.val,hi⟩)
    else
      Control.scope [.ref a,.ref b,.nat i.val,.bit false,.nat (i.val-a.size)]
        (b.observe (by simp only [size] at hw; omega)
          ⟨i.val-a.size,by have := i.isLt; simp only [size] at this; omega⟩)

theorem Chunks.observe_value (c : Chunks width) (hw : c.size ≤ 2^width) (i : Fin c.size) :
    (c.observe hw i).value = (c.read hw i).1 := by
  induction c with
  | leaf cells => rfl
  | zero n => rfl
  | join a b ia ib =>
    simp only [observe,read]
    split <;> simp_all only [Control.scope,indexM_exact,Resources.bind,ia,ib]

theorem Chunks.observe_peak (c : Chunks width) (hw : c.size ≤ 2^width) (i : Fin c.size) :
    (c.observe hw i).peak ≤ 5*c.depth+3 := by
  induction c with
  | leaf cells => rfl
  | zero n => simp [observe,Control.note,depth]
  | join a b ia ib =>
    have ha := Nat.le_max_left a.depth b.depth
    have hb := Nat.le_max_right a.depth b.depth
    simp only [observe,depth]
    split
    · have hh := ia (by simp only [size] at hw; omega) ⟨i.val,by assumption⟩
      simp only [Control.scope,List.length_cons,List.length_nil]
      omega
    · have hh := ib (by simp only [size] at hw; omega)
        ⟨i.val-a.size,by have := i.isLt; simp only [size] at this; omega⟩
      simp only [Control.scope,List.length_cons,List.length_nil]
      omega

def observeCell (c : Chunks width) (hw : c.size ≤ 2^width) (i : Nat) : Control.Run (Word width) :=
  Control.scope [.ref c,.nat i,.bit (decide (i<c.size))]
    (if hi : i<c.size then c.observe hw ⟨i,hi⟩ else Control.pure (word width 0))

def observeRun (c : Chunks width) (hw : c.size ≤ 2^width) (capacity : Nat) :=
  Control.tabulate (word width 0) (fun i : Fin capacity => observeCell c hw i.val)

theorem observeRun_value (c : Chunks width) (hw : c.size ≤ 2^width) (capacity : Nat) :
    (observeRun c hw capacity).value = (run c hw capacity).1 := by
  rw [observeRun,Control.tabulate_value,run,TableExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn,observeCell,cell,Control.scope]
  split <;> simp_all [Chunks.observe_value,Control.pure,Resources.pure]

theorem observeRun_peak (c : Chunks width) (hw : c.size ≤ 2^width) (capacity : Nat) :
    (observeRun c hw capacity).peak ≤ 5*c.depth+14 := by
  apply Control.tabulate_peak
  intro i
  simp only [observeCell,Control.scope,List.length_cons,List.length_nil]
  split
  · have hh := c.observe_peak hw ⟨i.val,by assumption⟩; omega
  · simp [Control.pure]

end Sequences.LCA.Materialize
