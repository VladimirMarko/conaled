import Applications.Parallel.FFTRounds

/-! Complete unitary matching layers and absorption of diagonal phases. -/
namespace Applications.Parallel.FFTUnitary

open scoped BigOperators Matrix

noncomputable def diagonalUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → _root_.unitary ℂ) : Matrix.unitaryGroup ι ℂ := by
  refine ⟨Matrix.diagonal (fun i => (d i : ℂ)), Matrix.diagonal_mem_unitary.mpr ?_⟩
  constructor
  · funext i
    exact (d i).property.1
  · funext i
    exact (d i).property.2

namespace Gate

variable {N : ℕ}

/-- Input phases are absorbed into the same two-coordinate block. -/
noncomputable def absorb (d : Fin N → _root_.unitary ℂ) (g : Gate N) : Gate N where
  frame := g.frame
  block := g.block * diagonalUnitary (fun i => d (g.coordinate i))

@[simp] theorem absorb_coordinate (d : Fin N → _root_.unitary ℂ) (g : Gate N) (i : Fin 2) :
    (absorb d g).coordinate i = g.coordinate i := rfl

end Gate

namespace Round

variable {N : ℕ}

noncomputable def absorb (d : Fin N → _root_.unitary ℂ) (r : Round N) : Round N where
  gates := r.gates.map (Gate.absorb d)
  disjoint := by simpa [List.pairwise_map] using r.disjoint

@[simp] theorem absorb_gateCount (d : Fin N → _root_.unitary ℂ) (r : Round N) :
    (absorb d r).gateCount = r.gateCount := by simp [absorb, gateCount]

theorem absorb_complete (d : Fin N → _root_.unitary ℂ) (r : Round N) (hr : r.Complete) :
    (absorb d r).Complete := by
  intro i
  obtain ⟨g, hg, t, ht⟩ := hr i
  exact ⟨Gate.absorb d g, List.mem_map_of_mem hg, t, ht⟩

/-- Completeness is essential: every diagonal phase is attached to exactly one gate.
The transformed matching uses the same coordinates and the same gate count. -/
theorem absorb_mul (d : Fin N → _root_.unitary ℂ) (r : Round N) (hr : r.Complete)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ((absorb d r).unitary : Matrix (Fin N) (Fin N) ℂ) * M =
      (r.unitary : Matrix (Fin N) (Fin N) ℂ) *
        ((diagonalUnitary d : Matrix (Fin N) (Fin N) ℂ) * M) := by
  ext i j
  simp only [unitary]
  obtain ⟨g, hg, t, rfl⟩ := hr i
  have hg' : Gate.absorb d g ∈ (absorb d r).gates := List.mem_map_of_mem hg
  change ((gatesUnitary (absorb d r).gates : Matrix (Fin N) (Fin N) ℂ) * M)
    ((Gate.absorb d g).coordinate t) j = _
  rw [matching_mul_coordinate _ (absorb d r).disjoint _ hg',
    matching_mul_coordinate _ r.disjoint _ hg]
  apply Finset.sum_congr rfl
  intro b _
  simp [Gate.absorb, Gate.coordinate, diagonalUnitary, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc]

theorem absorb_unitary (d : Fin N → _root_.unitary ℂ) (r : Round N) (hr : r.Complete) :
    (absorb d r).unitary = r.unitary * diagonalUnitary d := by
  apply Subtype.ext
  simpa using absorb_mul d r hr (1 : Matrix (Fin N) (Fin N) ℂ)

end Round

end Applications.Parallel.FFTUnitary
