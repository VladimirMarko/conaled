import SquareKit.SmoothTransversality
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Ordinary transverse fiber products with their original subtype topology. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTransversePullback
open ManifoldRealization SmoothTransversality SmoothRegularLevel Set Function
open scoped Manifold ContDiff Topology

abbrev Pullback {M N P : Type} (f : M → P) (g : N → P) :=
  {z : M × N // f z.1 = g z.2}

variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  [TopologicalSpace P] [ChartedSpace (Space p) P]
  {f : M → P} {g : N → P}

def fst (z : Pullback f g) : M := z.val.1
def snd (z : Pullback f g) : N := z.val.2

omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] in
theorem equation (z : Pullback f g) : f (fst z) = g (snd z) := z.property

omit [TopologicalSpace P] in
theorem continuous_fst : Continuous (fst : Pullback f g → M) :=
  _root_.continuous_fst.comp continuous_subtype_val

omit [TopologicalSpace P] in
theorem continuous_snd : Continuous (snd : Pullback f g → N) :=
  _root_.continuous_snd.comp continuous_subtype_val

abbrev derivative (q : Pullback f g) :=
  fderiv ℝ (coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2)
    (coordinateCenter (m := m) (n := n) q.val.1 q.val.2)

/-- Local analytic data, derived below from smoothness and derivative transversality. -/
structure LocalModel (q : Pullback f g) where
  normal : NormalForm (coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2)
    (derivative q) (coordinateCenter q.val.1 q.val.2)
    (coordinateNeighborhood (p := p) f g q.val.1 q.val.2)
  coordinates : (derivative (m := m) (n := n) (p := p) q).ker ≃L[ℝ] Space (m + n - p)

namespace LocalModel
variable {q : Pullback f g} (A : LocalModel (m := m) (n := n) (p := p) q)
attribute [local instance] Classical.propDecidable

def ambientChart (_A : LocalModel (m := m) (n := n) (p := p) q) :
    OpenPartialHomeomorph (M × N) (Space m × Space n) :=
  (chartAt (Space m) q.val.1).prod (chartAt (Space n) q.val.2)

theorem normal_source_subset : A.normal.chart.source ⊆ A.ambientChart.target :=
  fun _ hz => ⟨(A.normal.source_subset hz).1.1, (A.normal.source_subset hz).2.1⟩

def source : Set (Pullback f g) :=
  {z | z.val ∈ A.ambientChart.source ∧ A.ambientChart z.val ∈ A.normal.chart.source}

def target : Set (Space (m + n - p)) := A.coordinates.symm ⁻¹' A.normal.levelDomain

def forward (z : Pullback f g) : Space (m + n - p) :=
  A.coordinates (A.normal.projection (A.ambientChart z.val - coordinateCenter q.val.1 q.val.2))

def parameterize (v : Space (m + n - p)) : Space m × Space n :=
  A.normal.parameterize (A.coordinates.symm v)

theorem parameterize_source {v : Space (m + n - p)} (hv : v ∈ A.target) :
    A.parameterize v ∈ A.normal.chart.source := A.normal.parameterize_mem_source hv

theorem parameterize_equation {v : Space (m + n - p)} (hv : v ∈ A.target) :
    f (A.ambientChart.symm (A.parameterize v)).1 =
      g (A.ambientChart.symm (A.parameterize v)).2 := by
  apply (coordinateDifference_eq_zero_iff (A.normal.source_subset (A.parameterize_source hv))).mp
  exact (A.normal.parameterize_level hv).trans (coordinateDifference_center q.property)

def inverse (v : Space (m + n - p)) : Pullback f g :=
  if hv : v ∈ A.target then
    ⟨A.ambientChart.symm (A.parameterize v), A.parameterize_equation hv⟩ else q

theorem inverse_val {v : Space (m + n - p)} (hv : v ∈ A.target) :
    (A.inverse v).val = A.ambientChart.symm (A.parameterize v) := by
  simp only [inverse, dite_eq_left hv]

theorem source_level {z : Pullback f g} (hz : z ∈ A.source) :
    coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2
      (A.ambientChart z.val) =
    coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2
      (coordinateCenter (m := m) (n := n) q.val.1 q.val.2) := by
  rw [coordinateDifference_center q.property]
  apply (coordinateDifference_eq_zero_iff (A.normal.source_subset hz.2)).mpr
  change f (A.ambientChart.symm (A.ambientChart z.val)).1 =
    g (A.ambientChart.symm (A.ambientChart z.val)).2
  rw [A.ambientChart.left_inv hz.1]
  exact z.property

theorem forward_mem {z : Pullback f g} (hz : z ∈ A.source) : A.forward z ∈ A.target := by
  change A.coordinates.symm (A.coordinates _) ∈ A.normal.levelDomain
  rw [A.coordinates.symm_apply_apply]
  exact A.normal.coordinate_mem_levelDomain hz.2 (A.source_level hz)

theorem inverse_mem {v : Space (m + n - p)} (hv : v ∈ A.target) :
    A.inverse v ∈ A.source := by
  change (A.inverse v).val ∈ A.ambientChart.source ∧
    A.ambientChart (A.inverse v).val ∈ A.normal.chart.source
  rw [A.inverse_val hv]
  have ht := A.normal_source_subset (A.parameterize_source hv)
  refine ⟨A.ambientChart.map_target ht, ?_⟩
  rw [A.ambientChart.right_inv ht]
  exact A.parameterize_source hv

theorem inverse_forward {z : Pullback f g} (hz : z ∈ A.source) :
    A.inverse (A.forward z) = z := by
  apply Subtype.ext
  rw [A.inverse_val (A.forward_mem hz)]
  have hp : A.parameterize (A.forward z) = A.ambientChart z.val := by
    dsimp only [parameterize, forward]
    rw [A.coordinates.symm_apply_apply]
    exact A.normal.parameterize_recovery hz.2 (A.source_level hz)
  rw [hp, A.ambientChart.left_inv hz.1]

theorem forward_inverse {v : Space (m + n - p)} (hv : v ∈ A.target) :
    A.forward (A.inverse v) = v := by
  dsimp only [forward]
  rw [A.inverse_val hv, A.ambientChart.right_inv (A.normal_source_subset (A.parameterize_source hv))]
  dsimp only [parameterize]
  rw [A.normal.parameterize_coordinate hv, A.coordinates.apply_symm_apply]

theorem mem_source : q ∈ A.source :=
  ⟨⟨mem_chart_source _ _, mem_chart_source _ _⟩, A.normal.mem_source⟩

theorem isOpen_source : IsOpen A.source := by
  have ho := A.ambientChart.isOpen_inter_preimage A.normal.chart.open_source
  exact ho.preimage continuous_subtype_val

theorem isOpen_target : IsOpen A.target :=
  A.normal.isOpen_levelDomain.preimage A.coordinates.symm.continuous

theorem continuousOn_forward : ContinuousOn A.forward A.source := by
  have ha : ContinuousOn (fun z : Pullback f g => A.ambientChart z.val) A.source :=
    A.ambientChart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hz => hz.1)
  exact A.coordinates.continuous.comp_continuousOn
    (A.normal.projection.continuous.comp_continuousOn (ha.sub continuousOn_const))

theorem continuousOn_parameterize : ContinuousOn A.parameterize A.target :=
  A.normal.smooth_parameterize.continuousOn.comp A.coordinates.symm.continuous.continuousOn
    (fun _ hv => hv)

theorem continuousOn_inverse : ContinuousOn A.inverse A.target := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have ha : ContinuousOn (fun v => A.ambientChart.symm (A.parameterize v)) A.target :=
    A.ambientChart.continuousOn_symm.comp A.continuousOn_parameterize
      (fun _ hv => A.normal_source_subset (A.parameterize_source hv))
  have hc : Continuous (fun v : A.target =>
      (⟨A.ambientChart.symm (A.parameterize v.val), A.parameterize_equation v.property⟩ :
        Pullback f g)) := ha.domRestrict.subtype_mk _
  apply hc.congr
  intro v
  apply Subtype.ext
  exact (A.inverse_val v.property).symm

/-- The local chart on the actual equality subtype, with no global nonemptiness choice. -/
def chart : OpenPartialHomeomorph (Pullback f g) (Space (m + n - p)) where
  toFun := A.forward
  invFun := A.inverse
  source := A.source
  target := A.target
  map_source' _ h := A.forward_mem h
  map_target' _ h := A.inverse_mem h
  left_inv' _ h := A.inverse_forward h
  right_inv' _ h := A.forward_inverse h
  open_source := A.isOpen_source
  open_target := A.isOpen_target
  continuousOn_toFun := A.continuousOn_forward
  continuousOn_invFun := A.continuousOn_inverse

end LocalModel

variable [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N]
  [IsManifold (Model p) ∞ P]

/-- Pointwise transversality is required only at actual points of the fiber product. -/
def Transverse (f : M → P) (g : N → P) : Prop :=
  ∀ q : Pullback f g, TransverseAt (m := m) (n := n) (p := p) f g q.val.1 q.val.2 q.property

omit [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N]
  [IsManifold (Model p) ∞ P] in
theorem derivative_surjective
    (hf : ContMDiff (Model m) (Model p) ∞ f)
    (hg : ContMDiff (Model n) (Model p) ∞ g)
    (ht : Transverse (m := m) (n := n) (p := p) f g) (q : Pullback f g) :
    Surjective (derivative (m := m) (n := n) (p := p) q) :=
  (transverseAt_iff_coordinate_surjective ((hf _).mdifferentiableAt (by simp))
    ((hg _).mdifferentiableAt (by simp)) q.property).mp (ht q)

def localModel
    (hf : ContMDiff (Model m) (Model p) ∞ f)
    (hg : ContMDiff (Model n) (Model p) ∞ g)
    (ht : Transverse (m := m) (n := n) (p := p) f g) (q : Pullback f g) :
    LocalModel (m := m) (n := n) (p := p) q where
  normal := Classical.choice (nonempty_coordinateNormalForm hf hg q.property (ht q))
  coordinates := ContinuousLinearEquiv.ofFinrankEq (by
    rw [kernel_finrank (derivative q) (derivative_surjective hf hg ht q)]
    simp [Space])

omit [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N]
  [IsManifold (Model p) ∞ P] in
theorem dimension_inequality
    (hf : ContMDiff (Model m) (Model p) ∞ f)
    (hg : ContMDiff (Model n) (Model p) ∞ g)
    (ht : Transverse (m := m) (n := n) (p := p) f g) (q : Pullback f g) : p ≤ m + n := by
  have h := kernel_finrank_add (derivative q) (derivative_surjective hf hg ht q)
  simp only [Module.finrank_prod, Space, Module.finrank_fin_fun] at h
  omega

end SquareKit.SmoothTransversePullback
