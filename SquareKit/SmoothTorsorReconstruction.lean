import SquareKit.SmoothTorsorPrebundle
import SquareKit.SmoothLocalHomeomorph
import SquareKit.SmoothPrincipalBundle

/-! The ordinary total manifold reconstructed from a smooth sheaf torsor. -/
noncomputable section
namespace SquareKit.SmoothTorsorReconstruction
variable {B G : Type} [TopologicalSpace B] [TopologicalSpace G] [DiscreteTopology G]
private def productSheet (g : G) : OpenPartialHomeomorph (B × G) B where
  toFun := Prod.fst
  invFun b := (b,g)
  source := Set.univ ×ˢ {g}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := ⟨Set.mem_univ _, rfl⟩
  left_inv' z hz := by
    exact Prod.ext rfl (Set.mem_singleton_iff.mp hz.2).symm
  right_inv' _ _ := rfl
  open_source := isOpen_univ.prod (isOpen_discrete _)
  open_target := isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn
  continuousOn_invFun := (continuous_id.prodMk continuous_const).continuousOn
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open Topology ManifoldRealization SmoothOpenSite SmoothManifoldAction
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (Model n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
variable [TopologicalSpace G] [DiscreteTopology G]
instance totalTopology : TopologicalSpace (Total P) := (prebundle P).totalSpaceTopology
instance totalFiberBundle : FiberBundle G (Fiber P) := (prebundle P).toFiberBundle
def localProduct (i : (sectionCharts P).Index) : Bundle.Trivialization G
    (Bundle.TotalSpace.proj : Total P → B) :=
  (prebundle P).trivializationOfMemPretrivializationAtlas (show pretrivialization P i ∈
    (prebundle P).pretrivializationAtlas from ⟨i,rfl⟩)

def localSheet (i : (sectionCharts P).Index) (g : G) : OpenPartialHomeomorph (Total P) B :=
  (localProduct P i).toOpenPartialHomeomorph.trans (productSheet g)

def projectionSheets : SmoothLocalHomeomorph.ProjectionSheets
    (Bundle.TotalSpace.proj : Total P → B) where
  sheet z := localSheet P ((sectionCharts P).covers z.proj).choose
    ((productEquiv P (sectionValue P ((sectionCharts P).covers z.proj).choose) z).2)
  mem_source z := ⟨((sectionCharts P).covers z.proj).choose_spec, Set.mem_univ _, rfl⟩
  projection _ := rfl

@[instance_reducible]
def chartedSpace : ChartedSpace (Space n) (Total P) :=
  (projectionSheets P).chartedSpace (n := n)

theorem isManifold : letI := chartedSpace P; IsManifold (Model n) ∞ (Total P) :=
  (projectionSheets P).isManifold

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem smul_productEquiv_symm (s : ∀ b, Fiber P b) (g : G) (bg : B × G) :
    g • (productEquiv P s).symm bg = (productEquiv P s).symm (bg.1,g*bg.2) := by
  apply Bundle.TotalSpace.mk_inj.mpr
  change g • (bg.2 • s bg.1) = (g*bg.2) • s bg.1
  exact (mul_smul g bg.2 (s bg.1)).symm
theorem continuous_action (g : G) : Continuous (fun z : Total P => g • z) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨i,hi⟩ := (sectionCharts P).covers z.proj
  let e := localProduct P i
  have hz : z ∈ e.source := hi
  have htarget : ((e z).1,g*(e z).2) ∈ e.target := ⟨hi,Set.mem_univ _⟩
  have hm : Continuous (fun bg : B × G => (bg.1,g*bg.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hc : ContinuousAt (fun w : Total P =>
      e.toOpenPartialHomeomorph.symm ((e w).1,g*(e w).2)) z :=
    ContinuousAt.comp (f := fun w : Total P => ((e w).1,g*(e w).2))
      (e.toOpenPartialHomeomorph.continuousAt_symm htarget)
      (hm.continuousAt.comp (e.toOpenPartialHomeomorph.continuousAt hz))
  apply hc.congr
  apply Filter.Eventually.of_forall
  intro w
  have h := smul_productEquiv_symm P (sectionValue P i) g (productEquiv P (sectionValue P i) w)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

theorem localSheet_target (i : (sectionCharts P).Index) (g : G) :
    (localSheet P i g).target = ((sectionCharts P).chart i).source := by
  ext b
  change (b ∈ Set.univ ∧ (b,g) ∈ ((sectionCharts P).chart i).source ×ˢ Set.univ) ↔ _
  simp only [Set.mem_univ, Set.mem_prod, and_true, true_and]
theorem localSheet_projection (i : (sectionCharts P).Index) (g : G) :
    ⇑(localSheet P i g) = (Bundle.TotalSpace.proj : Total P → B) := rfl
theorem localSheet_inverse_projection (i : (sectionCharts P).Index) (g : G) (b : B) :
    ((localSheet P i g).symm b).proj = b := rfl
theorem smooth_localSheet_inverse (i : (sectionCharts P).Index) (g : G) :
    letI := chartedSpace P
    ContMDiffOn (Model n) (Model n) ∞ (localSheet P i g).symm
      ((sectionCharts P).chart i).source := by
  let := chartedSpace P
  intro b hb
  exact ((projectionSheets P).smooth_of_proj_at (localSheet P i g).symm b
    ((localSheet P i g).continuousAt_symm ((localSheet_target P i g).symm ▸ hb))
    (show ContMDiffAt (Model n) (Model n) ∞ id b from contMDiff_id b)).contMDiffWithinAt
def localTrivialization (i : (sectionCharts P).Index) :
    letI := chartedSpace P
    SmoothPrincipalBundle.LocalTrivialization (n := n) (G := G)
      (Bundle.TotalSpace.proj : Total P → B) := by
  letI := chartedSpace P
  exact {
    base := ((sectionCharts P).chart i).source
    isOpen_base := ((sectionCharts P).chart i).open_source
    sheet := localSheet P i
    target := localSheet_target P i
    projection := fun _ _ _ => rfl
    smooth_inverse := smooth_localSheet_inverse P i
    sheets := fun z hz => ⟨(productEquiv P (sectionValue P i) z).2,
      ⟨hz,Set.mem_univ _,rfl⟩, fun _ hh => hh.2.2.symm⟩
    equivariant := fun g h b _ => (smul_productEquiv_symm P (sectionValue P i) g (b,h)).symm }

def bundle : letI := chartedSpace P
    SmoothPrincipalBundle.Bundle (n := n) (G := G) (B := B) (E := Total P) := by
  letI := chartedSpace P
  exact {
    projection := Bundle.TotalSpace.proj
    smooth_projection := (projectionSheets P).smooth_proj
    smooth_action := fun g => (projectionSheets P).smooth_of_proj (fun z => g • z)
      (continuous_action P g) ((projectionSheets P).smooth_proj)
    invariant := fun _ _ => rfl
    triviality := fun b => by
      obtain ⟨i,hi⟩ := (sectionCharts P).covers b
      exact ⟨localTrivialization P i,hi⟩ }
end SquareKit.SmoothTorsorReconstruction
