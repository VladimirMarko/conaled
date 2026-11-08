import Applications.Sequences.LCA.Arena
import Applications.Sequences.LCA.KeyBounds

/-! Concrete descriptor-and-payload layout for finite word matrices. A row
lookup reads its descriptor, then reads a payload word at that base plus the
column. Nested instances supply the shared class/row hierarchy. -/
namespace Sequences.LCA.FlatTable
variable {cols : Nat} [NeZero cols]
open Dijkstra.Store

def words (rows cols : Nat) := rows + rows*cols

def pack (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (base capacity : Nat) (fit : base + words rows cols ≤ capacity)
    (wide : capacity ≤ 2^width) : Vector (Fin (2^width)) (words rows cols) :=
  (Vector.ofFn fun i : Fin rows =>
    (⟨base+rows+i.val*cols, by
      have hi := i.isLt
      have hm := Nat.mul_le_mul_right cols (show i.val+1 ≤ rows by omega)
      have hp := NeZero.pos cols
      unfold words at fit
      nlinarith⟩ : Fin (2^width))) ++ cells.flatten

omit [NeZero cols] in
theorem payload_index_lt (i : Fin rows) (j : Fin cols) :
    rows+i.val*cols+j.val < words rows cols := by
  have hm := Nat.mul_le_mul_right cols (show i.val+1 ≤ rows by omega)
  have hj := j.isLt
  unfold words
  nlinarith

theorem descriptor_read (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (fit : base + words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin rows) :
    ((pack cells base capacity fit wide)[i.val]'(by have := i.isLt; unfold words; omega)).val = base+rows+i.val*cols := by
  simp [pack, words, i.isLt]

theorem payload_read (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (fit : base + words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (i : Fin rows) (j : Fin cols) :
    (pack cells base capacity fit wide)[rows+i.val*cols+j.val]'(payload_index_lt i j) =
      cells[i.val][j.val] := by
  have hc : 0 < cols := Nat.zero_lt_of_lt j.isLt
  have hj := j.isLt
  have hi := i.isLt
  unfold words at *
  unfold pack
  erw [Vector.getElem_append_right (by exact payload_index_lt i j) (by omega)]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [Vector.getElem_flatten]
  have hd : (i.val*cols+j.val)/cols = i.val := by
    simpa [Nat.add_comm, Nat.mul_comm, Nat.div_eq_of_lt hj] using Nat.add_mul_div_left j.val i.val hc
  have hm : (i.val*cols+j.val)%cols = j.val := by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  simp [hd, hm]

def segment (fit : base + words rows cols ≤ capacity) : Arena.Segment capacity (words rows cols) :=
  ⟨base, fit⟩

def install (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (fit : base + words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) : Store capacity (Fin (2^width)) :=
  Arena.install (segment fit) (pack cells base capacity fit wide) arena

theorem installed_payload (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (fit : base + words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) (i : Fin rows) (j : Fin cols) :
    lookup (install cells fit wide arena)
      ((segment fit).address ⟨rows+i.val*cols+j.val, payload_index_lt i j⟩) = cells[i.val][j.val] := by
  rw [install, Arena.install_represents]
  exact payload_read cells fit wide i j

theorem installed_descriptor (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (fit : base + words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) (i : Fin rows) :
    (lookup (install cells fit wide arena)
      ((segment fit).address ⟨i.val, by have := i.isLt; unfold words; omega⟩)).val =
      base+rows+i.val*cols := by
  rw [install, Arena.install_represents]
  exact descriptor_read cells fit wide i

theorem payload_address_eq_descriptor (cells : Vector (Vector (Fin (2^width)) cols) rows)
    (fit : base + words rows cols ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) (i : Fin rows) (j : Fin cols) :
    ((segment fit).address ⟨rows+i.val*cols+j.val, payload_index_lt i j⟩).val =
      (lookup (install cells fit wide arena)
        ((segment fit).address ⟨i.val, by have := i.isLt; unfold words; omega⟩)).val+j.val := by
  rw [installed_descriptor]
  simp [segment, Arena.Segment.address, Nat.add_assoc]

def microMatrix (code : Fin (2^steps))
    (wide : (2*steps+1)*(2*(steps+1)) ≤ 2^width) :
    Vector (Vector (Fin (2^width)) (steps+1)) (steps+1) :=
  Vector.ofFn fun start => (KeyBounds.encodedMicroRow code start).map (Fin.castLE wide)

theorem microMatrix_read (code : Fin (2^steps))
    (wide : (2*steps+1)*(2*(steps+1)) ≤ 2^width) (start len : Fin (steps+1)) :
    ((microMatrix code wide)[start.val][len.val]).val =
      WordKey.encode (steps : Int) (2*(steps+1))
        (ofLex ((((prepareShared steps).get code).get start).get len)).1
        (ofLex ((((prepareShared steps).get code).get start).get len)).2 := by
  simpa [microMatrix] using KeyBounds.encodedMicroRow_read code start len

/-- An actual shared-class row layout, including word-encoded row pointers. -/
def installMicro (code : Fin (2^steps))
    (keyWidth : (2*steps+1)*(2*(steps+1)) ≤ 2^width)
    (fit : base + words (steps+1) (steps+1) ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) : Store capacity (Fin (2^width)) :=
  install (microMatrix code keyWidth) fit wide arena

theorem installMicro_read (code : Fin (2^steps))
    (keyWidth : (2*steps+1)*(2*(steps+1)) ≤ 2^width)
    (fit : base + words (steps+1) (steps+1) ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) (start len : Fin (steps+1)) :
    (lookup (installMicro code keyWidth fit wide arena)
      ((segment fit).address ⟨(steps+1)+start.val*(steps+1)+len.val,
        payload_index_lt start len⟩)).val =
      WordKey.encode (steps : Int) (2*(steps+1))
        (ofLex ((((prepareShared steps).get code).get start).get len)).1
        (ofLex ((((prepareShared steps).get code).get start).get len)).2 := by
  rw [installMicro, installed_payload]
  exact microMatrix_read code keyWidth start len

def sharedCells (steps base capacity : Nat)
    (keyWidth : (2*steps+1)*(2*(steps+1)) ≤ 2^width)
    (fit : base + words (2^steps) (words (steps+1) (steps+1)) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    Vector (Vector (Fin (2^width)) (words (steps+1) (steps+1))) (2^steps) :=
  Vector.ofFn fun code => pack (microMatrix code keyWidth)
    (base+2^steps+code.val*words (steps+1) (steps+1)) capacity (by
      have hm := Nat.mul_le_mul_right (words (steps+1) (steps+1))
        (show code.val+1 ≤ 2^steps by have := code.isLt; omega)
      unfold words at *
      nlinarith) wide

def sharedPack (steps base capacity : Nat)
    (keyWidth : (2*steps+1)*(2*(steps+1)) ≤ 2^width)
    (fit : base + words (2^steps) (words (steps+1) (steps+1)) ≤ capacity)
    (wide : capacity ≤ 2^width) :
    Vector (Fin (2^width)) (words (2^steps) (words (steps+1) (steps+1))) :=
  letI : NeZero (words (steps+1) (steps+1)) := ⟨by unfold words; omega⟩
  pack (sharedCells steps base capacity keyWidth fit wide) base capacity fit wide

theorem sharedPack_size (steps : Nat) :
    words (2^steps) (words (steps+1) (steps+1)) =
      2^steps*((steps+1)*(steps+1)+(steps+1)+1) := by unfold words; ring


theorem sharedPack_payload (steps base capacity : Nat)
    (keyWidth : (2*steps+1)*(2*(steps+1)) ≤ 2^width)
    (fit : base + words (2^steps) (words (steps+1) (steps+1)) ≤ capacity)
    (wide : capacity ≤ 2^width)
    (code : Fin (2^steps)) (start len : Fin (steps+1)) :
    (sharedPack steps base capacity keyWidth fit wide)[
      2^steps+code.val*words (steps+1) (steps+1)+((steps+1)+start.val*(steps+1)+len.val)]'
        (payload_index_lt code ⟨_, payload_index_lt start len⟩) =
      (microMatrix code keyWidth)[start.val][len.val] := by
  let : NeZero (words (steps+1) (steps+1)) := ⟨by unfold words; omega⟩
  unfold sharedPack
  erw [payload_read _ fit wide code ⟨_, payload_index_lt start len⟩]
  simp only [sharedCells, Vector.getElem_ofFn]
  exact payload_read _ _ wide start len


def macroMatrix (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n)
    (wide : (2*n)*(blocks*(steps+1)) ≤ 2^width) :
    Vector (Vector (Fin (2^width)) blocks) (levels+1) :=
  Vector.ofFn fun level =>
    (KeyBounds.encodedMacroRow depth hn hb hsteps hdepth hcap level).map (Fin.castLE wide)

theorem macroMatrix_read (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n)
    (wide : (2*n)*(blocks*(steps+1)) ≤ 2^width) (level : Fin (levels+1)) (i : Fin blocks) :
    ((macroMatrix depth hn hb hsteps hdepth hcap wide)[level.val][i.val]).val =
      WordKey.encode 0 (blocks*(steps+1))
        (ofLex (((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val]).1
        (ofLex (((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val]).2 := by
  simpa [macroMatrix] using KeyBounds.encodedMacroRow_read depth hn hb hsteps hdepth hcap level i

/-- Macro rows use the same finite descriptor-and-payload layout. Their span
and logarithm vectors are separate finite arrays in the macro region. -/
def installMacro (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n)
    (keyWidth : (2*n)*(blocks*(steps+1)) ≤ 2^width)
    (fit : base + words (levels+1) blocks ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) : Store capacity (Fin (2^width)) :=
  letI : NeZero blocks := ⟨by omega⟩
  install (macroMatrix depth hn hb hsteps hdepth hcap keyWidth) fit wide arena


theorem installMacro_read (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n)
    (keyWidth : (2*n)*(blocks*(steps+1)) ≤ 2^width)
    (fit : base + words (levels+1) blocks ≤ capacity) (wide : capacity ≤ 2^width)
    (arena : Store capacity (Fin (2^width))) (level : Fin (levels+1)) (i : Fin blocks) :
    lookup (installMacro depth hn hb hsteps hdepth hcap keyWidth fit wide arena)
      ((segment fit).address ⟨(levels+1)+level.val*blocks+i.val,
        payload_index_lt level i⟩) =
      (macroMatrix depth hn hb hsteps hdepth hcap keyWidth)[level.val][i.val] := by
  let : NeZero blocks := ⟨by omega⟩
  exact installed_payload _ fit wide arena level i

example :
    ((sharedPack 2 0 128 (by decide : 30 ≤ 2^8) (by decide) (by decide))[23]).val = 14 := by
  erw [sharedPack_payload 2 0 128 _ _ _ (1 : Fin 4) (1 : Fin 3) (1 : Fin 3)]
  rw [microMatrix_read (steps := 2) 1 _ 1 1]
  decide


example :
    (pack (microMatrix (steps := 2) 1 (by decide : 30 ≤ 2^8)) 10 64
      (by decide) (by decide))[1].val = 16 := by
  erw [descriptor_read _ _ _ (1 : Fin 3)]
  decide

example :
    (lookup (installMicro (steps := 2) 1 (by decide : 30 ≤ 2^8)
      (base := 10) (capacity := 64) (by decide) (by decide)
      (Arena.initialized 64 8))
      ((segment (base := 10) (by decide : 10+words 3 3 ≤64)).address
        ⟨7, by decide⟩)).val = 14 := by
  erw [installMicro_read (steps := 2) 1 _ _ _ _ (1 : Fin 3) (1 : Fin 3)]
  decide

end Sequences.LCA.FlatTable
