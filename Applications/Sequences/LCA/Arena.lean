import Applications.Dijkstra.Store
import Mathlib.Tactic

/-! A finite flat arena interprets disjoint local store addresses. The cells
read/write algebra commutes with this interpretation, so the table loops need
no assumption that nested Lean arrays themselves are the target RAM. -/
namespace Sequences.LCA.Arena
open Dijkstra.Store
variable {α : Type}

structure Segment (capacity length : Nat) where
  base : Nat
  fits : base+length ≤ capacity

def Segment.address (s : Segment capacity length) (i : Fin length) : Fin capacity :=
  ⟨s.base+i.val, by have := s.fits; have := i.isLt; omega⟩

theorem Segment.address_injective (s : Segment capacity length) : Function.Injective s.address := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [Segment.address] at hh
  omega

def Represents (s : Segment capacity length) (cells : Store length α) (arena : Store capacity α) : Prop :=
  ∀ i, lookup arena (s.address i) = lookup cells i

theorem read_simulates (s : Segment capacity length) (cells : Store length α) (arena : Store capacity α)
    (h : Represents s cells arena) (i : Fin length) : lookup arena (s.address i) = lookup cells i := h i

theorem write_simulates (s : Segment capacity length) (cells : Store length α) (arena : Store capacity α)
    (h : Represents s cells arena) (i : Fin length) (value : α) :
    Represents s (write cells i value) (write arena (s.address i) value) := by
  intro j
  rw [lookup_write, lookup_write]
  have he : s.address i = s.address j ↔ i = j := s.address_injective.eq_iff
  simp only [he, h j]

def Disjoint (s : Segment capacity a) (t : Segment capacity b) : Prop :=
  s.base+a ≤ t.base ∨ t.base+b ≤ s.base

theorem disjoint_addresses (s : Segment capacity a) (t : Segment capacity b)
    (h : Disjoint s t) (i : Fin a) (j : Fin b) : s.address i ≠ t.address j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  simp only [Segment.address] at hv
  rcases h with h | h <;> omega

theorem other_segment_preserved (s : Segment capacity a) (t : Segment capacity b)
    (h : Disjoint s t) (cells : Store b α) (arena : Store capacity α)
    (hr : Represents t cells arena) (i : Fin a) (value : α) :
    Represents t cells (write arena (s.address i) value) := by
  intro j
  rw [lookup_write, ite_eq_right (disjoint_addresses s t h i j)]
  exact hr j

/-- Install a local segment into an existing finite arena. The target addresses
are exactly the segment addresses; unrelated addresses keep their values. -/
def install (s : Segment capacity length) (cells : Store length α)
    (arena : Store capacity α) : Store capacity α :=
  Vector.ofFn fun j => if h : s.base ≤ j.val ∧ j.val < s.base+length then
    lookup cells ⟨j.val-s.base, by omega⟩ else lookup arena j

theorem install_represents (s : Segment capacity length) (cells : Store length α)
    (arena : Store capacity α) : Represents s cells (install s cells arena) := by
  intro i
  have hi := i.isLt
  simp [install, lookup, Segment.address, hi]

theorem install_other (s : Segment capacity a) (t : Segment capacity b)
    (h : Disjoint s t) (cells : Store a α) (other : Store b α)
    (arena : Store capacity α) (hr : Represents t other arena) :
    Represents t other (install s cells arena) := by
  intro j
  have hj := j.isLt
  have hn : ¬(s.base ≤ (t.address j).val ∧ (t.address j).val < s.base+a) := by
    simp only [Segment.address]
    rcases h with h | h <;> omega
  simpa [install, lookup, hn] using hr j

/-- An initialized arena witnesses a nonempty state space for every finite
capacity and word width; subsequent writes remain in `Fin (2^width)`. -/
def initialized (capacity width : Nat) : Store capacity (Fin (2^width)) :=
  Vector.replicate capacity ⟨0, Nat.two_pow_pos width⟩

theorem initialized_read (i : Fin capacity) :
    (lookup (initialized capacity width) i).val = 0 := by simp [lookup, initialized]

private def first : Segment 4 2 := ⟨0, by decide⟩
private def second : Segment 4 2 := ⟨2, by decide⟩

example : Represents first (#[7, 3].toVector)
    (install first (#[7, 3].toVector) (Vector.replicate 4 0)) :=
  install_represents _ _ _

example : lookup
    (write (install second (#[5, 9].toVector) (Vector.replicate 4 0))
      (first.address 1) 8) (second.address 0) = 5 := by decide

example : Disjoint first second := Or.inl (by decide)

end Sequences.LCA.Arena
