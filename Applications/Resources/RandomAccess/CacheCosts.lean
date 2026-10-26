import Applications.Sequences.RandomAccess.TreeBuild

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

theorem structuralSize_erasure (t : Tree α) :
    Bracketing.size (erase t) = (fromT t).length := by
  rw [fromT_eq_fringe, Bracketing.fringeSpec_length]

/-- The smart constructor preserves correct caches without assuming perfection. -/
theorem cached_node {l r : Tree α} (hl : Cached l) (hr : Cached r) :
    Cached (node l r) := ⟨rfl, hl, hr⟩

/-- Actual uncached size evaluation, charging one visited tree constructor. -/
def structuralSizeRun : Bracketing.Tree α → Nat × Nat
  | .leaf _ => (1, 1)
  | .fork l r =>
      let left := structuralSizeRun l
      let right := structuralSizeRun r
      (left.1 + right.1, left.2 + right.2 + 1)

theorem structuralSizeRun_value (t : Bracketing.Tree α) :
    (structuralSizeRun t).1 = Bracketing.size t := by
  induction t with
  | leaf x => rfl
  | fork l r ihl ihr => simp [structuralSizeRun, Bracketing.size, ihl, ihr]

theorem structuralSizeRun_work (t : Bracketing.Tree α) :
    (structuralSizeRun t).2 + 1 = 2 * Bracketing.size t := by
  induction t with
  | leaf x => rfl
  | fork l r ihl ihr =>
    simp only [structuralSizeRun, Bracketing.size]
    omega

/-- The installed cache is selected directly, with one selector event. -/
def cachedSizeRun : Tree α → Nat × Nat
  | .leaf _ => (1, 1)
  | .node n _ _ => (n, 1)

theorem cachedSizeRun_exact (t : Tree α) : cachedSizeRun t = (size t, 1) := by
  cases t <;> rfl

/-- Equal answers under Cached, with explicitly different evaluation work. -/
theorem size_run_comparison (t : Tree α) (h : Cached t) :
    (structuralSizeRun (erase t)).1 = (cachedSizeRun t).1 ∧
      (structuralSizeRun (erase t)).2 + 1 = 2 * (cachedSizeRun t).1 ∧
      (cachedSizeRun t).2 = 1 := by
  rw [cachedSizeRun_exact, structuralSizeRun_value, structuralSizeRun_work,
    cached_size_erasure t h]
  exact ⟨rfl, rfl, rfl⟩

end Resources.RandomAccessCosts
