import SquareKit.SmoothTransversePullback
import Mathlib.Topology.Bases

/-! Smooth atlas and universal smoothness for ordinary transverse fiber products.

`chartedSpace` and `isManifold` construct the ordinary manifold needed for the
all-stage comparison in issue #97. `smooth_fst`, `smooth_snd`, `smooth_lift` and
`lift_unique` specify its actual projections and ordinary universal property.
No sheaf pullback preservation is asserted here. The model is `Space (m+n-p)`
also for empty fibers; only an actual point gives the rank inequality.
-/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTransversePullback
open ManifoldRealization SmoothTransversality SmoothRegularLevel Set Function
open scoped Manifold ContDiff Topology
variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]
  [TopologicalSpace P] [ChartedSpace (Space p) P] [IsManifold (modelWithCorners p) ∞ P]
  {f : M → P} {g : N → P}

namespace LocalModel
variable {q : Pullback f g} (A : LocalModel (m := m) (n := n) (p := p) q)

omit [IsManifold (modelWithCorners m) ∞ M] [IsManifold (modelWithCorners n) ∞ N]
  [IsManifold (modelWithCorners p) ∞ P] in
theorem smooth_parameterize {v : Space (m + n - p)} (hv : v ∈ A.target) :
    ContDiffAt ℝ ∞ A.parameterize v :=
  (A.normal.smooth_parameterize.contDiffAt
    (A.normal.isOpen_levelDomain.mem_nhds hv)).comp v A.coordinates.symm.contDiff.contDiffAt

omit [IsManifold (modelWithCorners n) ∞ N] [IsManifold (modelWithCorners p) ∞ P] in
theorem smooth_inverse_fst {v : Space (m + n - p)} (hv : v ∈ A.target) :
    ContMDiffAt (modelWithCorners (m+n-p)) (modelWithCorners m) ∞ (fst ∘ A.inverse) v := by
  have ht := A.normal_source_subset (A.parameterize_source hv)
  have hs := (contMDiffOn_chart_symm (I := modelWithCorners m) (n := ∞) (x := q.val.1)).contMDiffAt
    ((chartAt (Space m) q.val.1).open_target.mem_nhds ht.1)
  have hp := (A.smooth_parameterize hv).fst.contMDiffAt
  apply (hs.comp v hp).congr_of_eventuallyEq
  filter_upwards [A.isOpen_target.mem_nhds hv] with w hw
  exact congrArg Prod.fst (A.inverse_val hw)

omit [IsManifold (modelWithCorners m) ∞ M] [IsManifold (modelWithCorners p) ∞ P] in
theorem smooth_inverse_snd {v : Space (m + n - p)} (hv : v ∈ A.target) :
    ContMDiffAt (modelWithCorners (m+n-p)) (modelWithCorners n) ∞ (snd ∘ A.inverse) v := by
  have ht := A.normal_source_subset (A.parameterize_source hv)
  have hs := (contMDiffOn_chart_symm (I := modelWithCorners n) (n := ∞) (x := q.val.2)).contMDiffAt
    ((chartAt (Space n) q.val.2).open_target.mem_nhds ht.2)
  have hp := (A.smooth_parameterize hv).snd.contMDiffAt
  apply (hs.comp v hp).congr_of_eventuallyEq
  filter_upwards [A.isOpen_target.mem_nhds hv] with w hw
  exact congrArg Prod.snd (A.inverse_val hw)

omit [IsManifold (modelWithCorners p) ∞ P] in
theorem smooth_forward_comp {k : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (Space k) X] (h : X → Pullback f g) (x : X)
    (hfst : ContMDiffAt (modelWithCorners k) (modelWithCorners m) ∞ (fst ∘ h) x)
    (hsnd : ContMDiffAt (modelWithCorners k) (modelWithCorners n) ∞ (snd ∘ h) x)
    (hx : h x ∈ A.source) :
    ContMDiffAt (modelWithCorners k) (modelWithCorners (m+n-p)) ∞ (A.forward ∘ h) x := by
  have hs := ((contMDiffOn_chart (I := modelWithCorners m) (n := ∞) (x := q.val.1)).contMDiffAt
    ((chartAt (Space m) q.val.1).open_source.mem_nhds hx.1.1)).comp x hfst
  have ht := ((contMDiffOn_chart (I := modelWithCorners n) (n := ∞) (x := q.val.2)).contMDiffAt
    ((chartAt (Space n) q.val.2).open_source.mem_nhds hx.1.2)).comp x hsnd
  have hp := (hs.prodMk_space ht).sub
    (contMDiffAt_const (c := coordinateCenter (m := m) (n := n) q.val.1 q.val.2))
  exact A.coordinates.contDiff.contMDiff.contMDiffAt.comp x
    (A.normal.projection.contDiff.contMDiff.contMDiffAt.comp x hp)

end LocalModel
variable (hf : ContMDiff (modelWithCorners m) (modelWithCorners p) ∞ f)
  (hg : ContMDiff (modelWithCorners n) (modelWithCorners p) ∞ g)
  (ht : Transverse (m := m) (n := n) (p := p) f g)

/-- The point-indexed normal forms cover the equality subtype, including the empty case. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (Space (m+n-p)) (Pullback f g) where
  atlas := Set.range (fun q => (localModel hf hg ht q).chart)
  chartAt q := (localModel hf hg ht q).chart
  mem_chart_source q := (localModel hf hg ht q).mem_source
  chart_mem_atlas q := ⟨q, rfl⟩

theorem isManifold :
    letI := chartedSpace hf hg ht
    IsManifold (modelWithCorners (m+n-p)) ∞ (Pullback f g) := by
  let := chartedSpace hf hg ht
  apply isManifold_of_contDiffOn (modelWithCorners (m+n-p)) ∞ (Pullback f g)
  rintro e e' ⟨q, rfl⟩ ⟨r, rfl⟩
  simp only [modelWithCorners, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  intro v hv
  exact ((localModel hf hg ht r).smooth_forward_comp
    (localModel hf hg ht q).inverse v
    ((localModel hf hg ht q).smooth_inverse_fst hv.1)
    ((localModel hf hg ht q).smooth_inverse_snd hv.1) hv.2).contDiffAt.contDiffWithinAt

theorem smooth_fst :
    letI := chartedSpace hf hg ht
    ContMDiff (modelWithCorners (m+n-p)) (modelWithCorners m) ∞ (fst : Pullback f g → M) := by
  let := chartedSpace hf hg ht
  intro q
  apply contMDiffAt_iff_source.mpr
  exact ((localModel hf hg ht q).smooth_inverse_fst
    ((localModel hf hg ht q).forward_mem (localModel hf hg ht q).mem_source)).contMDiffWithinAt

theorem smooth_snd :
    letI := chartedSpace hf hg ht
    ContMDiff (modelWithCorners (m+n-p)) (modelWithCorners n) ∞ (snd : Pullback f g → N) := by
  let := chartedSpace hf hg ht
  intro q
  apply contMDiffAt_iff_source.mpr
  exact ((localModel hf hg ht q).smooth_inverse_snd
    ((localModel hf hg ht q).forward_mem (localModel hf hg ht q).mem_source)).contMDiffWithinAt

theorem smooth_of_components_at {k : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (Space k) X] (h : X → Pullback f g) (x : X)
    (hfst : ContMDiffAt (modelWithCorners k) (modelWithCorners m) ∞ (fst ∘ h) x)
    (hsnd : ContMDiffAt (modelWithCorners k) (modelWithCorners n) ∞ (snd ∘ h) x) :
    letI := chartedSpace hf hg ht
    ContMDiffAt (modelWithCorners k) (modelWithCorners (m+n-p)) ∞ h x := by
  let := chartedSpace hf hg ht
  apply contMDiffAt_iff_target.mpr
  refine ⟨?_, ?_⟩
  · exact (hfst.continuousAt.prodMk hsnd.continuousAt).codRestrict _
  · exact (localModel hf hg ht (h x)).smooth_forward_comp h x hfst hsnd
      (localModel hf hg ht (h x)).mem_source

theorem smooth_iff_components {k : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (Space k) X] (h : X → Pullback f g) :
    letI := chartedSpace hf hg ht
    ContMDiff (modelWithCorners k) (modelWithCorners (m+n-p)) ∞ h ↔
      ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ (fst ∘ h) ∧
      ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ (snd ∘ h) := by
  let := chartedSpace hf hg ht
  exact ⟨fun hh => ⟨(smooth_fst hf hg ht).comp hh, (smooth_snd hf hg ht).comp hh⟩,
    fun hh x => smooth_of_components_at hf hg ht h x (hh.1 x) (hh.2 x)⟩

/-- The ordinary lift is the compatible pair itself. -/
def lift {X : Type} (u : X → M) (v : X → N) (h : ∀ x, f (u x) = g (v x)) :
    X → Pullback f g := fun x => ⟨(u x, v x), h x⟩

omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] in
@[simp] theorem lift_fst {X : Type} (u : X → M) (v : X → N)
    (h : ∀ x, f (u x) = g (v x)) : fst ∘ lift u v h = u := rfl

omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] in
@[simp] theorem lift_snd {X : Type} (u : X → M) (v : X → N)
    (h : ∀ x, f (u x) = g (v x)) : snd ∘ lift u v h = v := rfl

omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] in
theorem lift_unique {X : Type} (u : X → M) (v : X → N)
    (h : ∀ x, f (u x) = g (v x)) (w : X → Pullback f g)
    (hw₁ : fst ∘ w = u) (hw₂ : snd ∘ w = v) : w = lift u v h := by
  funext x
  exact Subtype.ext (Prod.ext (congrFun hw₁ x) (congrFun hw₂ x))

theorem smooth_lift {k : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (Space k) X] (u : X → M) (v : X → N)
    (h : ∀ x, f (u x) = g (v x))
    (hu : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ u)
    (hv : ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ v) :
    letI := chartedSpace hf hg ht
    ContMDiff (modelWithCorners k) (modelWithCorners (m+n-p)) ∞ (lift u v h) :=
  (smooth_iff_components hf hg ht _).mpr ⟨hu, hv⟩

omit [TopologicalSpace P] in
/-- Separation is inherited from the source product, without a target hypothesis. -/
theorem t2Space [T2Space M] [T2Space N] : T2Space (Pullback f g) := inferInstance

omit [TopologicalSpace P] in
/-- Countability is inherited from the source product, independently of the atlas. -/
theorem secondCountableTopology [SecondCountableTopology M] [SecondCountableTopology N] :
    SecondCountableTopology (Pullback f g) :=
  TopologicalSpace.Subtype.secondCountableTopology {z : M × N | f z.1 = g z.2}

end SquareKit.SmoothTransversePullback
