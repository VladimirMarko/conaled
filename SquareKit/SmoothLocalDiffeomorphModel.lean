import Applications.Orbifolds.LocalBranches
import SquareKit.SmoothLocalHomeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! A local diffeomorphism to a finite-real manifold supplies a compatible finite-real model. -/
noncomputable section
open Set Topology
open scoped Manifold ContDiff
namespace SquareKit
open ManifoldRealization

namespace SmoothLocalHomeomorph.ProjectionSheets
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
  {n : ℕ} [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
  {p : E → B} (S : SmoothLocalHomeomorph.ProjectionSheets p)
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
  {IN : ModelWithCorners ℝ EN HN}

/-- The projection criterion accepts an arbitrary source model. -/
theorem smooth_of_proj_at_model (h : N → E) (x : N) (hc : ContinuousAt h x)
    (hs : ContMDiffAt IN (modelWithCorners n) ∞ (p ∘ h) x) :
    letI := S.chartedSpace (n := n)
    ContMDiffAt IN (modelWithCorners n) ∞ h x := by
  let := S.chartedSpace (n := n)
  apply contMDiffAt_iff_target.mpr
  refine ⟨hc, ?_⟩
  change ContMDiffAt IN (modelWithCorners n) ∞
    ((chartAt (Space n) (p (h x))) ∘ (S.sheet (h x) ∘ h)) x
  rw [S.projection]
  exact (contMDiffOn_chart (I := modelWithCorners n) (x := p (h x))).contMDiffAt
    ((chartAt (Space n) (p (h x))).open_source.mem_nhds
      (mem_chart_source _ _)) |>.comp x hs

theorem smooth_of_proj_model (h : N → E) (hc : Continuous h)
    (hs : ContMDiff IN (modelWithCorners n) ∞ (p ∘ h)) :
    letI := S.chartedSpace (n := n)
    ContMDiff IN (modelWithCorners n) ∞ h :=
  fun x => S.smooth_of_proj_at_model h x hc.continuousAt (hs x)

end SmoothLocalHomeomorph.ProjectionSheets

namespace SmoothLocalDiffeomorphModel
variable {EA HA : Type*} {A X : Type}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [TopologicalSpace HA] [TopologicalSpace A] [TopologicalSpace X]
  [ChartedSpace HA A] {IA : ModelWithCorners ℝ EA HA}
  {n : ℕ} [ChartedSpace (Space n) X]
  (s : A → X) (hs : IsLocalDiffeomorph IA (modelWithCorners n) ∞ s)

/-- The same points and topology, with charts induced by the local source projection. -/
def Model (_s : A → X) (_hs : IsLocalDiffeomorph IA (modelWithCorners n) ∞ _s) : Type := A

instance modelTopology : TopologicalSpace (Model s hs) := inferInstanceAs (TopologicalSpace A)

instance modelT2 [T2Space A] : T2Space (Model s hs) := inferInstanceAs (T2Space A)

instance modelSecondCountable [SecondCountableTopology A] :
    SecondCountableTopology (Model s hs) := inferInstanceAs (SecondCountableTopology A)

/-- Identity on the actual points, viewed in the induced finite-real model. -/
def toModel (a : A) : Model s hs := a

/-- Identity on points back to the original manifold. -/
def fromModel (a : Model s hs) : A := a

@[simp] theorem fromModel_toModel (a : A) : fromModel s hs (toModel s hs a) = a := rfl
@[simp] theorem toModel_fromModel (a : Model s hs) : toModel s hs (fromModel s hs a) = a := rfl

/-- Local projection sheets are derived from the supplied local diffeomorphism. -/
def sheets : SmoothLocalHomeomorph.ProjectionSheets (fun a : Model s hs => s (fromModel s hs a)) where
  sheet a := Classical.choose (hs.isLocalHomeomorph (fromModel s hs a))
  mem_source a := (Classical.choose_spec (hs.isLocalHomeomorph (fromModel s hs a))).1
  projection a := (Classical.choose_spec (hs.isLocalHomeomorph (fromModel s hs a))).2.symm

instance modelCharts : ChartedSpace (Space n) (Model s hs) := (sheets s hs).chartedSpace

instance modelManifold [IsManifold (modelWithCorners n) ∞ X] :
    IsManifold (modelWithCorners n) ∞ (Model s hs) := (sheets s hs).isManifold

variable [IsManifold (modelWithCorners n) ∞ X]

theorem toModel_smooth : ContMDiff IA (modelWithCorners n) ∞ (toModel s hs) :=
  (sheets s hs).smooth_of_proj_model (toModel s hs) continuous_id hs.contMDiff

theorem projection_smooth : ContMDiff (modelWithCorners n) (modelWithCorners n) ∞
    (fun a : Model s hs => s (fromModel s hs a)) := (sheets s hs).smooth_proj

theorem fromModel_smooth : ContMDiff (modelWithCorners n) IA ∞ (fromModel s hs) := by
  intro a
  let h := hs (fromModel s hs a)
  have hi : ContMDiffAt (modelWithCorners n) IA ∞ h.localInverse
      (s (fromModel s hs a)) := h.contMDiffOn_localInverse.contMDiffAt
    (h.localInverse.open_source.mem_nhds h.localInverse_mem_source)
  have hc := hi.comp a (projection_smooth s hs a)
  apply hc.congr_of_eventuallyEq
  have he := h.localInverse_eventuallyEq_left
  exact (he.comp_tendsto (show ContinuousAt (fromModel s hs) a from continuousAt_id)).symm

/-- The native and induced models are related by the actual identity in both directions. -/
def diffeomorph : Diffeomorph IA (modelWithCorners n) A (Model s hs) ∞ where
  toFun := toModel s hs
  invFun := fromModel s hs
  left_inv := fromModel_toModel s hs
  right_inv := toModel_fromModel s hs
  contMDiff_toFun := toModel_smooth s hs
  contMDiff_invFun := fromModel_smooth s hs

@[simp] theorem diffeomorph_apply (a : A) : diffeomorph s hs a = toModel s hs a := rfl

@[simp] theorem diffeomorph_symm_apply (a : Model s hs) :
    (diffeomorph s hs).symm a = fromModel s hs a := rfl

/-- The actual source remains a local diffeomorphism after changing the arrow model. -/
theorem projection_localDiffeomorph :
    IsLocalDiffeomorph (modelWithCorners n) (modelWithCorners n) ∞
      (fun a : Model s hs => s (fromModel s hs a)) := by
  intro a
  obtain ⟨q,ha,hq⟩ := hs (fromModel s hs a)
  refine ⟨(diffeomorph s hs).symm.toPartialDiffeomorph.trans q, ⟨Set.mem_univ _,ha⟩, ?_⟩
  intro b hb
  exact hq hb.2

section Diagram
variable {Y J : Type} [TopologicalSpace Y] {t : A → Y}
  {U : TopologicalSpace.Opens X} {V : TopologicalSpace.Opens Y}
  (D : Orbifolds.LocalBranches.Diagram IA (modelWithCorners n) s t U V J)

/-- The induced-model copy of an open native branch piece. -/
def modelPiece (i : J) : TopologicalSpace.Opens (Model s hs) :=
  ⟨fromModel s hs ⁻¹' D.piece i, (D.piece i).isOpen.preimage continuous_id⟩

/-- Identity on a branch piece in both smooth models. -/
def pieceDiffeomorph (i : J) :
    Diffeomorph (modelWithCorners n) IA (modelPiece s hs D i) (D.piece i) ∞ where
  toFun z := ⟨fromModel s hs z.val, z.property⟩
  invFun z := ⟨toModel s hs z.val, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((fromModel_smooth s hs).comp (contMDiff_subtype_val (U := modelPiece s hs D i)))
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((toModel_smooth s hs).comp (contMDiff_subtype_val (U := D.piece i)))

/-- Transport a native branch diagram without changing any labels or domains. -/
def diagram : Orbifolds.LocalBranches.Diagram (modelWithCorners n) (modelWithCorners n)
    (fun a : Model s hs => s (fromModel s hs a))
    (fun a : Model s hs => t (fromModel s hs a)) U V J where
  piece := modelPiece s hs D
  domain := D.domain
  sourceEquiv i := (pieceDiffeomorph s hs D i).trans (D.sourceEquiv i)
  source_eq i z := D.source_eq i (pieceDiffeomorph s hs D i z)
  domain_le := D.domain_le
  target_mem i z := D.target_mem i (pieceDiffeomorph s hs D i z)
  disjoint := by
    intro i j hij
    apply TopologicalSpace.Opens.coe_disjoint.mp
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (D.disjoint hij)) hi hj
  covers a := D.covers (fromModel s hs a)

@[simp] theorem diagram_assemble (i : J) (z : D.domain i) :
    ((diagram s hs D).assemble i z).val = toModel s hs (D.assemble i z).val := rfl

@[simp] theorem diagram_branch (i : J) (z : D.domain i) :
    (diagram s hs D).branch i z = D.branch i z := rfl

end Diagram

end SmoothLocalDiffeomorphModel
end SquareKit
