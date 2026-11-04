import Applications.Sequences.LCA.PackedReads

/-! The declared finite-word query machine. An indexed read performs address
formation and one memory access. Its out-of-range case totalizes the otherwise
undefined machine operation; admitted execution proofs establish every address
is in range. Arithmetic writes wrap to the word width, so simulation must prove
that the intended intermediate values fit. -/
namespace Sequences.LCA.WordMachine
open Resources Dijkstra.Store
abbrev Word (width : Nat) := Fin (2^width)

def word (width value : Nat) : Word width := ⟨value % 2^width, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def scalar (width value : Nat) : Measured (Word width) Nat := (word width value,1)
def load (mem : Store capacity (Word width)) (base index : Nat) : Measured (Word width) Nat :=
  (if h : base+index < capacity then lookup mem ⟨base+index,h⟩ else word width 0,1)
def minimum (a b : Word width) : Measured (Word width) Nat := (min a b,1)
def pack (stride : Nat) (depth index : Word width) : Measured (Word width) Nat :=
  bind (scalar width (depth.val*stride)) fun product => scalar width (product.val+index.val)

theorem word_of_lt (h : value < 2^width) : (word width value).val = value := Nat.mod_eq_of_lt h
@[simp] theorem scalar_cost (width value : Nat) : (scalar width value).2 = 1 := rfl
@[simp] theorem load_cost (mem : Store capacity (Word width)) (base index : Nat) :
    (load mem base index).2 = 1 := rfl
@[simp] theorem minimum_cost (a b : Word width) : (minimum a b).2 = 1 := rfl
@[simp] theorem pack_cost (stride : Nat) (depth index : Word width) :
    (pack stride depth index).2 = 2 := rfl

theorem load_at (mem : Store capacity (Word width)) (i : Fin capacity) :
    (load mem 0 i.val).1 = lookup mem i := by simp [load]

theorem load_eq (mem : Store capacity (Word width)) (base index : Nat)
    (i : Fin capacity) (he : base+index=i.val) : (load mem base index).1 = lookup mem i := by
  simp [load, he, i.isLt]

theorem pack_value (stride : Nat) (depth index : Word width)
    (hm : depth.val*stride < 2^width) (ha : depth.val*stride+index.val < 2^width) :
    (pack stride depth index).1.val = depth.val*stride+index.val := by
  simp [pack, Resources.bind, scalar, word_of_lt hm, word_of_lt ha]

end Sequences.LCA.WordMachine
