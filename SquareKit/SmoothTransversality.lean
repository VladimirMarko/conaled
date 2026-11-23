import SquareKit.SmoothManifoldCharts
import SquareKit.SmoothRegularLevel
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Derivative transversality and the regular-level equation in a common target chart. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTransversality
open ManifoldRealization Set Function
open scoped Manifold ContDiff Topology

variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  [TopologicalSpace P] [ChartedSpace (Space p) P]

/-- Transport a tangent vector only along an equality of its base points. -/
def tangentTransport {a b : P} (h : a = b) :
    TangentSpace (Model p) a ≃L[ℝ] TangentSpace (Model p) b := by
  subst b
  exact ContinuousLinearEquiv.refl ℝ _

@[simp] theorem tangentTransport_apply {a b : P} (h : a = b)
    (v : TangentSpace (Model p) a) : tangentTransport h v = v := by
  subst b
  rfl

/-- The derivative difference has one target tangent space, using the given equality. -/
def tangentDifference (f : M → P) (g : N → P) (x : M) (y : N) (h : f x = g y) :
    (TangentSpace (Model m) x × TangentSpace (Model n) y) →L[ℝ]
      TangentSpace (Model p) (f x) :=
  (mfderiv (Model m) (Model p) f x).comp (ContinuousLinearMap.fst ℝ _ _) -
    (tangentTransport h.symm).toContinuousLinearMap.comp
      ((mfderiv (Model n) (Model p) g y).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Ordinary derivative transversality at an equal-image pair. -/
def TransverseAt (f : M → P) (g : N → P) (x : M) (y : N) (h : f x = g y) : Prop :=
  Surjective (tangentDifference (m := m) (n := n) (p := p) f g x y h)

/-- The manifold derivative expressed in the preferred chart coordinates. -/
def chartDerivative (f : M → P) (x : M) : Space m →L[ℝ] Space p :=
  (tangentSpaceCastModel (Model p) (f x)).toContinuousLinearMap.comp
    ((mfderiv (Model m) (Model p) f x).comp
      (tangentSpaceCastModel (Model m) x).symm.toContinuousLinearMap)

def coordinateLinearDifference (f : M → P) (g : N → P) (x : M) (y : N) :
    (Space m × Space n) →L[ℝ] Space p :=
  (chartDerivative f x).comp (ContinuousLinearMap.fst ℝ _ _) -
    (chartDerivative g y).comp (ContinuousLinearMap.snd ℝ _ _)

theorem coordinateLinearDifference_surjective_iff
    {f : M → P} {g : N → P} {x : M} {y : N} (h : f x = g y) :
    Surjective (coordinateLinearDifference (m := m) (n := n) (p := p) f g x y) ↔
      TransverseAt (m := m) (n := n) (p := p) f g x y h := by
  change (∀ z, ∃ v, _ = z) ↔ (∀ z, ∃ v, _ = z)
  simp only [coordinateLinearDifference, chartDerivative, tangentDifference,
    sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, tangentTransport_apply]
  rfl

/-- Both maps are read in the chart centered at `f x`. -/
def coordinateDifference (f : M → P) (g : N → P) (x : M) (y : N) :
    Space m × Space n → Space p := fun z =>
  (chartAt (Space p) (f x)) (f ((chartAt (Space m) x).symm z.1)) -
  (chartAt (Space p) (f x)) (g ((chartAt (Space n) y).symm z.2))

def coordinateCenter (x : M) (y : N) : Space m × Space n :=
  ((chartAt (Space m) x) x, (chartAt (Space n) y) y)

/-- The actual neighborhood on which both source charts and the common target chart apply. -/
def coordinateNeighborhood (f : M → P) (g : N → P) (x : M) (y : N) :
    Set (Space m × Space n) :=
  coordinateOpen (e := chartAt (Space m) x) (chartAt (Space p) (f x)) f ×ˢ
    coordinateOpen (e := chartAt (Space n) y) (chartAt (Space p) (f x)) g

theorem coordinateNeighborhood_isOpen {f : M → P} {g : N → P}
    (hf : Continuous f) (hg : Continuous g) (x : M) (y : N) :
    IsOpen (coordinateNeighborhood (m := m) (n := n) (p := p) f g x y) :=
  (coordinateOpen_open _ f hf).prod (coordinateOpen_open _ g hg)

theorem coordinateCenter_mem {f : M → P} {g : N → P} {x : M} {y : N}
    (h : f x = g y) : coordinateCenter (m := m) (n := n) x y ∈ coordinateNeighborhood (m := m) (n := n) (p := p) f g x y := by
  simp only [coordinateNeighborhood, coordinateOpen, coordinateCenter, Set.mem_prod,
    Set.mem_inter_iff, Set.mem_preimage,
    (chartAt (Space m) x).left_inv (mem_chart_source _ _),
    (chartAt (Space n) y).left_inv (mem_chart_source _ _)]
  exact ⟨⟨mem_chart_target _ _, mem_chart_source _ _⟩,
    ⟨mem_chart_target _ _, h ▸ mem_chart_source _ _⟩⟩

theorem coordinateDifference_center {f : M → P} {g : N → P} {x : M} {y : N}
    (h : f x = g y) : coordinateDifference (m := m) (n := n) (p := p) f g x y (coordinateCenter (m := m) (n := n) x y) = 0 := by
  simp only [coordinateDifference, coordinateCenter,
    (chartAt (Space m) x).left_inv (mem_chart_source _ _),
    (chartAt (Space n) y).left_inv (mem_chart_source _ _), h, sub_self]

theorem coordinateDifference_eq_zero_iff {f : M → P} {g : N → P} {x : M} {y : N}
    {z : Space m × Space n} (hz : z ∈ coordinateNeighborhood (m := m) (n := n) (p := p) f g x y) :
    coordinateDifference (m := m) (n := n) (p := p) f g x y z = 0 ↔
      f ((chartAt (Space m) x).symm z.1) = g ((chartAt (Space n) y).symm z.2) := by
  rw [coordinateDifference, sub_eq_zero]
  exact ⟨fun he => (chartAt (Space p) (f x)).injOn hz.1.2 hz.2.2 he, congrArg _⟩

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_coordinateDifference {f : M → P} {g : N → P} {x : M} {y : N}
    (hf : MDifferentiableAt (Model m) (Model p) f x)
    (hg : MDifferentiableAt (Model n) (Model p) g y) (h : f x = g y) :
    HasFDerivAt (coordinateDifference (m := m) (n := n) (p := p) f g x y)
      (coordinateLinearDifference (m := m) (n := n) (p := p) f g x y)
      (coordinateCenter (m := m) (n := n) x y) := by
  have hf' := hf.hasMFDerivAt.2
  have hg' := hg.hasMFDerivAt.2
  simp only [Model, modelWithCornersSelf_coe, range_id, hasFDerivWithinAt_univ,
    writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] at hf' hg'
  have hg'' : HasFDerivAt
      ((chartAt (Space p) (f x)) ∘ g ∘ (chartAt (Space n) y).symm)
      (chartDerivative (m := n) (p := p) g y) ((chartAt (Space n) y) y) := by
    simpa only [h, chartDerivative, ContinuousLinearMap.comp_assoc] using hg'
  have hfst : HasFDerivAt (Prod.fst : Space m × Space n → Space m)
      (ContinuousLinearMap.fst ℝ _ _) (coordinateCenter (m := m) (n := n) x y) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : Space m × Space n → Space n)
      (ContinuousLinearMap.snd ℝ _ _) (coordinateCenter (m := m) (n := n) x y) :=
    hasFDerivAt_snd
  exact (hf'.comp (coordinateCenter (m := m) (n := n) x y) hfst).sub
    (hg''.comp (coordinateCenter (m := m) (n := n) x y) hsnd)

theorem transverseAt_iff_coordinate_surjective {f : M → P} {g : N → P} {x : M} {y : N}
    (hf : MDifferentiableAt (Model m) (Model p) f x)
    (hg : MDifferentiableAt (Model n) (Model p) g y) (h : f x = g y) :
    TransverseAt (m := m) (n := n) (p := p) f g x y h ↔
      Surjective (fderiv ℝ (coordinateDifference (m := m) (n := n) (p := p) f g x y) (coordinateCenter (m := m) (n := n) x y)) := by
  rw [(hasFDerivAt_coordinateDifference hf hg h).fderiv]
  exact (coordinateLinearDifference_surjective_iff h).symm

theorem coordinateDifference_contDiffOn
    [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N] [IsManifold (Model p) ∞ P]
    {f : M → P} {g : N → P}
    (hf : ContMDiff (Model m) (Model p) ∞ f)
    (hg : ContMDiff (Model n) (Model p) ∞ g) (x : M) (y : N) :
    ContDiffOn ℝ ∞ (coordinateDifference (m := m) (n := n) (p := p) f g x y)
      (coordinateNeighborhood (m := m) (n := n) (p := p) f g x y) := by
  intro z hz
  have hs := (contMDiffOn_chart_symm (I := Model m) (n := ∞) (x := x)).contMDiffAt
    ((chartAt (Space m) x).open_target.mem_nhds hz.1.1)
  have ht := (contMDiffOn_chart_symm (I := Model n) (n := ∞) (x := y)).contMDiffAt
    ((chartAt (Space n) y).open_target.mem_nhds hz.2.1)
  have hf' := ((contMDiffOn_chart (I := Model p) (n := ∞) (x := f x)).contMDiffAt
    ((chartAt (Space p) (f x)).open_source.mem_nhds hz.1.2)).comp z.1
      ((hf _).comp z.1 hs)
  have hg' := ((contMDiffOn_chart (I := Model p) (n := ∞) (x := f x)).contMDiffAt
    ((chartAt (Space p) (f x)).open_source.mem_nhds hz.2.2)).comp z.2
      ((hg _).comp z.2 ht)
  exact ((hf'.contDiffAt.comp z contDiffAt_fst).sub
    (hg'.contDiffAt.comp z contDiffAt_snd)).contDiffWithinAt

/-- Smooth maps transverse at an equal-image pair give a smooth regular-level normal form
for their actual common-chart equality equation. -/
theorem nonempty_coordinateNormalForm
    [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N] [IsManifold (Model p) ∞ P]
    {f : M → P} {g : N → P}
    (hf : ContMDiff (Model m) (Model p) ∞ f)
    (hg : ContMDiff (Model n) (Model p) ∞ g) {x : M} {y : N} (h : f x = g y)
    (ht : TransverseAt (m := m) (n := n) (p := p) f g x y h) :
    Nonempty (SmoothRegularLevel.NormalForm
      (coordinateDifference (m := m) (n := n) (p := p) f g x y)
      (fderiv ℝ (coordinateDifference (m := m) (n := n) (p := p) f g x y)
        (coordinateCenter (m := m) (n := n) x y))
      (coordinateCenter (m := m) (n := n) x y)
      (coordinateNeighborhood (m := m) (n := n) (p := p) f g x y)) :=
  SmoothRegularLevel.nonempty_normalForm_fderiv
    (coordinateNeighborhood_isOpen hf.continuous hg.continuous x y)
    (coordinateCenter_mem h) (coordinateDifference_contDiffOn hf hg x y)
    ((transverseAt_iff_coordinate_surjective
      ((hf x).mdifferentiableAt (by simp)) ((hg y).mdifferentiableAt (by simp)) h).mp ht)

end SquareKit.SmoothTransversality
