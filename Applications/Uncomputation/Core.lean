import SquareKit.Category

/-! A clean-workspace argument needs an inverse on admitted states and a use
that respects the computed dependency. No coordinate or cartesian structure is
assumed. Initialization is a separate morphism, never an invertible gate. -/
namespace Uncomputation

open SquareKit
universe u v

/-- Compute, use, then undo computation. Composition runs right to left. -/
def cleanup {O : Type u} (C : CategoryOps.{u,v} O) {a : O}
    (compute use undo : C.Hom a a) : C.Hom a a :=
  C.comp undo (C.comp use compute)

/-- `use_ok` specifies use on the computed clean subspace. `undo_ok` needs
only a left inverse there. The independently supplied `output` is retained. -/
theorem cleanup_correct {O : Type u} (C : CategoryOps.{u,v} O)
    (L : CategoryLaws C (equality C)) {a s : O}
    (compute use undo : C.Hom a a) (init : C.Hom s a) (output : C.Hom s s)
    (undo_ok : C.comp undo (C.comp compute init) = init)
    (use_ok : C.comp use (C.comp compute init) =
      C.comp (C.comp compute init) output) :
    C.comp (cleanup C compute use undo) init = C.comp init output := by
  change C.comp (C.comp undo (C.comp use compute)) init = _
  rw [L.assoc, L.assoc, use_ok, ← L.assoc, undo_ok]

/-- A concrete dependency-preserving use, including a caller-owned output.
The compute permutation can use any scratch type; only its zero slice matters. -/
theorem preserved_dependency {X T Y : Type} (compute : (X × T) ≃ (X × T))
    (zero : T) (dependency : X → T) (use : T → Y → Y)
    (computed : ∀ x, compute (x, zero) = (x, dependency x)) (x : X) (y : Y) :
    (compute.symm (compute (x, zero)), use (compute (x, zero)).2 y) =
      ((x, zero), use (dependency x) y) := by
  simp [computed]
  exact (compute.symm_apply_eq).mpr (computed x).symm

end Uncomputation
