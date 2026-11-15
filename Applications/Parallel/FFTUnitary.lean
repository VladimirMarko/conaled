import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Fin.Basic

/-! In-place complex circuits with two-coordinate unitary gates. -/

namespace Applications.Parallel.FFTUnitary

open scoped BigOperators

/-- A coordinate frame selects an ordered pair and enumerates the untouched registers.
It is a bijection, so it supplies neither copying nor workspace. -/
structure Gate (N : ℕ) where
  frame : Fin N ≃ Fin 2 ⊕ Fin (N - 2)
  block : Matrix.unitaryGroup (Fin 2) ℂ

namespace Gate

variable {N : ℕ}

def coordinate (g : Gate N) (i : Fin 2) : Fin N := g.frame.symm (.inl i)

theorem coordinate_injective (g : Gate N) : Function.Injective g.coordinate :=
  g.frame.symm.injective.comp Sum.inl_injective

theorem coordinates_distinct (g : Gate N) : g.coordinate 0 ≠ g.coordinate 1 := by
  intro h
  have := g.coordinate_injective h
  norm_num at this

/-- Every ordered pair of distinct registers is representable by a gate frame. -/
theorem exists_frame (e : Fin 2 ↪ Fin N) :
    ∃ f : Fin N ≃ Fin 2 ⊕ Fin (N - 2), ∀ i, f.symm (.inl i) = e i := by
  have hn : 2 ≤ N := by
    simpa using Fintype.card_le_of_injective e e.injective
  let b : Fin 2 ⊕ Fin (N - 2) ≃ Fin N :=
    finSumFinEquiv.trans (finCongr (by omega))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 2 => b (.inl i)) e
    (b.injective.comp Sum.inl_injective) e.injective
  exact ⟨(b.trans p).symm, hp⟩

noncomputable def ofPair (e : Fin 2 ↪ Fin N)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) : Gate N where
  frame := (exists_frame e).choose
  block := U

@[simp] theorem ofPair_coordinate (e : Fin 2 ↪ Fin N)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (ofPair e U).coordinate i = e i :=
  (exists_frame e).choose_spec i

noncomputable def matrix (g : Gate N) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks (g.block : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    (1 : Matrix (Fin (N - 2)) (Fin (N - 2)) ℂ)).submatrix g.frame g.frame

theorem matrix_unitary (g : Gate N) : g.matrix ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  apply Matrix.submatrix_equiv_mem_unitary.mpr
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp g.block.property,
    Matrix.fromBlocks_one]

noncomputable def unitary (g : Gate N) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨g.matrix, g.matrix_unitary⟩

end Gate

/-- A partial matching. Gates in a round act on disjoint register pairs. -/
structure Round (N : ℕ) where
  gates : List (Gate N)
  disjoint : gates.Pairwise (fun g h => ∀ i j, g.coordinate i ≠ h.coordinate j)

namespace Round

variable {N : ℕ}

def gateCount (r : Round N) : ℕ := r.gates.length

noncomputable def gatesUnitary : List (Gate N) → Matrix.unitaryGroup (Fin N) ℂ
  | [] => 1
  | g :: gs => gatesUnitary gs * g.unitary

noncomputable def unitary (r : Round N) : Matrix.unitaryGroup (Fin N) ℂ :=
  gatesUnitary r.gates

def Complete (r : Round N) : Prop :=
  ∀ i, ∃ g ∈ r.gates, ∃ j, g.coordinate j = i

end Round

/-- Register permutations are free. Each matching round is counted once. -/
inductive Step (N : ℕ) where
  | permute (p : Equiv.Perm (Fin N))
  | round (r : Round N)

namespace Step

variable {N : ℕ}

noncomputable def unitary : Step N → Matrix.unitaryGroup (Fin N) ℂ
  | .round r => r.unitary
  | .permute p => ⟨(1 : Matrix (Fin N) (Fin N) ℂ).submatrix p id,
      (Matrix.submatrix_equiv_mem_unitary (e₁ := p) (e₂ := Equiv.refl _)).mpr
        (one_mem (Matrix.unitaryGroup (Fin N) ℂ))⟩

def gateCount : Step N → ℕ
  | .round r => r.gateCount
  | .permute _ => 0

def roundCount : Step N → ℕ
  | .round _ => 1
  | .permute _ => 0

end Step

abbrev Program (N : ℕ) := List (Step N)

namespace Program

variable {N : ℕ}

noncomputable def unitary : Program N → Matrix.unitaryGroup (Fin N) ℂ
  | [] => 1
  | s :: ss => unitary ss * s.unitary

def gateCount (p : Program N) : ℕ := (p.map Step.gateCount).sum

def roundCount (p : Program N) : ℕ := (p.map Step.roundCount).sum

end Program

/-- There is no admissible gate on a single register. -/
theorem no_gate_one (g : Gate 1) : False :=
  g.coordinates_distinct (Subsingleton.elim _ _)

example : Program.gateCount ([] : Program 1) = 0 ∧
    Program.roundCount ([] : Program 1) = 0 ∧ Program.unitary ([] : Program 1) = 1 := by
  simp [Program.gateCount, Program.roundCount, Program.unitary]


end Applications.Parallel.FFTUnitary
