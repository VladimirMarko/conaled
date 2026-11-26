import SquareKit.SmoothTransversePullbackSmooth
import SquareKit.SmoothLocalHomeomorph

/-! Identity base change compares the regular-level and projection-sheet atlases. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTransversePullback
open ManifoldRealization SmoothTransversality SmoothLocalHomeomorph
open scoped Manifold ContDiff

variable {m n : ℕ} {P N : Type}
  [TopologicalSpace P] [ChartedSpace (Space m) P] [IsManifold (modelWithCorners m) ∞ P]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]
  (g : N → P)

omit [IsManifold (modelWithCorners m) ∞ P] [IsManifold (modelWithCorners n) ∞ N] in
theorem identity_transverse : Transverse (m := m) (n := n) (p := m) (id : P → P) g := by
  intro q v
  refine ⟨(v, 0), ?_⟩
  simp only [tangentDifference, sub_apply, ContinuousLinearMap.comp_apply, mfderiv_id,
    ContinuousLinearMap.id_apply]
  change v - (tangentTransport q.property.symm) ((mfderiv (modelWithCorners n) (modelWithCorners m) g q.val.2) 0) = v
  rw [map_zero, map_zero]
  exact sub_zero v

def identityHomeomorph (hg : Continuous g) : Pullback (id : P → P) g ≃ₜ N where
  toFun := snd
  invFun y := ⟨(g y, y), rfl⟩
  left_inv q := Subtype.ext (Prod.ext q.property.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := (hg.prodMk continuous_id).subtype_mk _

def identitySheets (hg : Continuous g) : ProjectionSheets (snd : Pullback (id : P → P) g → N) where
  sheet _ := (identityHomeomorph g hg).toOpenPartialHomeomorph
  mem_source _ := Set.mem_univ _
  projection _ := rfl

variable (hg : ContMDiff (modelWithCorners n) (modelWithCorners m) ∞ g)

/-- The general regular-level atlas detects smoothness through the second projection
in this local-diffeomorphism subclass, with no continuity premise. -/
theorem identity_regular_smooth_iff {k : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (Space k) X]
    (h : X → Pullback (id : P → P) g) :
    (letI := chartedSpace contMDiff_id hg (identity_transverse g);
      ContMDiff (modelWithCorners k) (modelWithCorners (m+n-m)) ∞ h) ↔
      ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ (snd ∘ h) := by
  rw [smooth_iff_components]
  refine ⟨And.right, fun hs => ⟨?_, hs⟩⟩
  have he : fst ∘ h = g ∘ (snd ∘ h) := funext fun x => (h x).property
  rw [he]
  exact hg.comp hs

omit [IsManifold (modelWithCorners m) ∞ P] in
/-- The same criterion for the independently constructed projection-sheet atlas. -/
theorem identity_sheets_smooth_iff {k : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (Space k) X]
    (h : X → Pullback (id : P → P) g) :
    (letI := (identitySheets g hg.continuous).chartedSpace (n := n);
      ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ h) ↔
      ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ (snd ∘ h) := by
  rw [ProjectionSheets.smooth_iff_proj]
  refine ⟨And.right, fun hs => ⟨?_, hs⟩⟩
  have he : h = (identityHomeomorph g hg.continuous).symm ∘ (snd ∘ h) := by
    funext x
    exact ((identityHomeomorph g hg.continuous).symm_apply_apply (h x)).symm
  rw [he]
  exact (identityHomeomorph g hg.continuous).symm.continuous.comp hs.continuous

/-- Both constructions recognize exactly the same smooth maps, even when the base
and total source model dimensions differ. -/
theorem identity_atlas_comparison {k : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (Space k) X]
    (h : X → Pullback (id : P → P) g) :
    (letI := chartedSpace contMDiff_id hg (identity_transverse g);
      ContMDiff (modelWithCorners k) (modelWithCorners (m+n-m)) ∞ h) ↔
    (letI := (identitySheets g hg.continuous).chartedSpace (n := n);
      ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ h) :=
  (identity_regular_smooth_iff g hg h).trans (identity_sheets_smooth_iff g hg h).symm

end SquareKit.SmoothTransversePullback
