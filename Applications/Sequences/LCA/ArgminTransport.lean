import Applications.Sequences.LCA.Micro

namespace Sequences.LCA
open PreparedRMQ

theorem rangeMin_depthKey (depth : Nat → Int) (start len : Nat) :
    rangeMin (depthKey depth) start len = depthKey depth (argmin depth start len) := by
  obtain ⟨i, hi, he⟩ := rangeMin_occurs (depthKey depth) start len
  simp [argmin, he, depthKey]

theorem argmin_shift (depth : Nat → Int) (offset start len : Nat) :
    offset + argmin (fun i => depth (offset+i)) start len =
      argmin depth (offset+start) len := by
  apply leftmostMinimum_unique depth (lo := offset+start) (hi := offset+start+len)
  · have h := argmin_correct (fun i => depth (offset+i)) start len
    have hlo := h.1
    have hhi := h.2.1
    refine ⟨by omega, by omega, ?_⟩
    intro j hj hj'
    have hh := h.2.2 (j-offset) (by omega) (by omega)
    have he : offset+(j-offset) = j := by omega
    dsimp only at hh
    rw [he] at hh
    exact ⟨hh.1, fun heq => by have := hh.2 heq; omega⟩
  · exact argmin_correct depth (offset+start) len

theorem leftmostMinimum_congr (a b : Nat → Int) (lo hi answer : Nat)
    (h : ∀ i, lo ≤ i → i ≤ hi → a i = b i)
    (hm : LeftmostMinimum a lo hi answer) : LeftmostMinimum b lo hi answer := by
  refine ⟨hm.1, hm.2.1, ?_⟩
  intro j hj hj'
  have hh := hm.2.2 j hj hj'
  simpa only [h answer hm.1 hm.2.1, h j hj hj'] using hh

end Sequences.LCA
