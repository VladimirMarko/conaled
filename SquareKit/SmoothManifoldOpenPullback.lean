import SquareKit.SmoothTransverseRealization
import SquareKit.SmoothManifoldDiffeomorph

/-! Realization preserves restriction to open subsets of a target manifold. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Set
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization

variable {m n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]

omit [IsManifold (modelWithCorners n) ∞ N] in
/-- An inherited open submanifold includes by a local diffeomorphism. -/
theorem open_inclusion_etale (V : Opens N) :
    IsLocalDiffeomorph (modelWithCorners n) (modelWithCorners n) ∞
      (Subtype.val : V → N) := by
  intro x
  let e := V.openPartialHomeomorphSubtypeCoe ⟨x⟩
  let q : PartialDiffeomorph (modelWithCorners n) (modelWithCorners n) V N ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff V _ _ _).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact e.right_inv hz
      · exact e.right_inv hy }
  exact ⟨q, Set.mem_univ x, fun _ _ => rfl⟩

namespace OpenPullback
variable (f : M → N)
  (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (V : Opens N)

/-- The actual open preimage, carrying the inherited atlas. -/
def domain : Opens M := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩

def restricted (x : domain f hf V) : V := ⟨f x.val, x.property⟩

omit [IsManifold (modelWithCorners m) ∞ M] [IsManifold (modelWithCorners n) ∞ N] in
theorem restricted_smooth :
    ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ (restricted f hf V) :=
  (ContMDiff.subtypeVal_comp_iff V _).mp (hf.comp contMDiff_subtype_val)

omit [IsManifold (modelWithCorners m) ∞ M] [IsManifold (modelWithCorners n) ∞ N] in
/-- Openness supplies the transversality needed by the existing realization theorem. -/
theorem transverse : SmoothTransversePullback.Transverse
    (m := m) (n := n) (p := n) f (Subtype.val : V → N) := by
  intro q v
  let e := (open_inclusion_etale (n := n) V q.val.2).mfderivToContinuousLinearEquiv (by simp)
  let w := SmoothTransversality.tangentTransport q.property (-v)
  refine ⟨(0, e.symm w), ?_⟩
  change (mfderiv (modelWithCorners m) (modelWithCorners n) f q.val.1) 0 -
    SmoothTransversality.tangentTransport q.property.symm
      ((mfderiv (modelWithCorners n) (modelWithCorners n)
        (Subtype.val : V → N) q.val.2) (e.symm w)) = v
  change _ - SmoothTransversality.tangentTransport q.property.symm
    (e (e.symm w)) = v
  rw [e.apply_symm_apply]
  simp only [map_zero, zero_sub]
  have transport_inverse {b c : N} (h : b = c)
      (z : TangentSpace (modelWithCorners n) b) :
      SmoothTransversality.tangentTransport h.symm
        (SmoothTransversality.tangentTransport h z) = z := by
    subst c
    rfl
  rw [show SmoothTransversality.tangentTransport q.property.symm w = -v from
    transport_inverse q.property (-v), neg_neg]

open SmoothTransversePullback in
/-- The regular-level atlas and the inherited open atlas describe the same maps. -/
def regularEquiv :
    letI := SmoothTransversePullback.chartedSpace hf (contMDiff_subtype_val (U := V)) (transverse f V)
    Diffeomorph (modelWithCorners m) (modelWithCorners (m+n-n))
      (domain f hf V) (Pullback f (Subtype.val : V → N)) ∞ := by
  letI := SmoothTransversePullback.chartedSpace hf (contMDiff_subtype_val (U := V)) (transverse f V)
  refine {
    toFun := fun x => ⟨(x.val, restricted f hf V x), rfl⟩
    invFun := fun q => ⟨q.val.1, (show f q.val.1 ∈ V from q.property.symm ▸ q.val.2.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun q => Subtype.ext (Prod.ext rfl (Subtype.ext q.property))
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · exact smooth_lift hf contMDiff_subtype_val (transverse f V)
      Subtype.val (restricted f hf V) (fun _ => rfl)
      contMDiff_subtype_val (restricted_smooth f hf V)
  · apply (ContMDiff.subtypeVal_comp_iff (domain f hf V) _).mp
    exact smooth_fst hf contMDiff_subtype_val (transverse f V)

/-- Restricting the target to an open subset gives an all-stage sheaf pullback. -/
theorem isPullback :
    IsPullback (map (Subtype.val : domain f hf V → M) contMDiff_subtype_val)
      (map (restricted f hf V) (restricted_smooth f hf V))
      (map f hf) (map (Subtype.val : V → N) contMDiff_subtype_val) := by
  let := SmoothTransversePullback.chartedSpace hf
    (contMDiff_subtype_val (U := V)) (transverse f V)
  let := SmoothTransversePullback.isManifold hf
    (contMDiff_subtype_val (U := V)) (transverse f V)
  apply (SmoothTransversePullback.Realization.isPullback hf
    contMDiff_subtype_val (transverse f V)).of_iso'
      (diffeomorphIso (regularEquiv f hf V)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [diffeomorphIso, SmoothTransversePullback.Realization.first,
      ← map_comp, Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [diffeomorphIso, SmoothTransversePullback.Realization.second,
      ← map_comp, Iso.refl_hom, Category.comp_id]
    rfl
  · simp
  · simp

end OpenPullback
end SquareKit.ManifoldRealization
