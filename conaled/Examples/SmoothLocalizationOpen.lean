import SquareKit.SmoothLocalizationOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental geometric localization clients. The reciprocal on the punctured
line fails to extend continuously at zero, but has a smooth inverse-graph extension. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Examples.SmoothLocalizationOpen
open SquareKit.SmoothAlgebra SquareKit.SmoothAlgebra.Localization

abbrev coordinate : Free 1 := generator 0

def reciprocal : Functions coordinate := ⟨fun x => (x.val 0)⁻¹, by
  apply (OpenFunctions.representative_iff _ (fun x => (x 0)⁻¹) (fun _ => rfl)).mpr
  exact (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).contDiffOn.inv (fun _ hx => hx)⟩

theorem reciprocal_is_inverse : fromOpen coordinate reciprocal = inverse coordinate := by
  apply (toOpen_bijective coordinate).injective
  have h := congrArg (fun k : Hom (Functions coordinate) (Functions coordinate) => k reciprocal)
    (toOpen_fromOpen coordinate)
  change toOpen coordinate (fromOpen coordinate reciprocal) = reciprocal at h
  rw [h]
  apply OpenFunctions.ext
  intro x
  exact (toOpen_inverse coordinate x).symm

theorem reciprocal_graph_extension :
    ∃ H : Free 2, ∀ x : locus coordinate,
      H.val (SquareKit.SmoothInverseGraph.graph coordinate.val x.val) = reciprocal.val x := by
  obtain ⟨H,hH⟩ := graphRestriction_surjective coordinate reciprocal
  exact ⟨H,fun x => congrArg (fun q : Functions coordinate => q.val x) hH⟩

/-- Even continuity at the missing boundary point is impossible for an extension. -/
theorem reciprocal_no_continuous_extension (G : ℝ → ℝ)
    (hG : ∀ x, x ≠ 0 → G x = x⁻¹) : ¬ContinuousAt G 0 := by
  intro hc
  have he : (fun x : ℝ => x*G x) =ᶠ[𝓝[≠] 0] (fun _ => 1) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hG x hx,mul_inv_cancel₀ hx]
  have h0 : Tendsto (fun x : ℝ => x*G x) (𝓝[≠] 0) (𝓝 (0*G 0)) :=
    (continuousAt_id.mul hc).tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun x : ℝ => x*G x) (𝓝[≠] 0) (𝓝 1) :=
    tendsto_const_nhds.congr' he.symm
  have hh := tendsto_nhds_unique h0 h1
  norm_num at hh

def exponentialReciprocal : Functions coordinate := ⟨fun x => Real.exp ((x.val 0)⁻¹), by
  apply (OpenFunctions.representative_iff _ (fun x => Real.exp ((x 0)⁻¹)) (fun _ => rfl)).mpr
  exact Real.contDiff_exp.comp_contDiffOn
    ((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).contDiffOn.inv (fun _ hx => hx))⟩

theorem exponentialReciprocal_recovered :
    toOpen coordinate (fromOpen coordinate exponentialReciprocal) = exponentialReciprocal :=
  congrArg (fun k : Hom (Functions coordinate) (Functions coordinate) => k exponentialReciprocal)
    (toOpen_fromOpen coordinate)

/-- The analytic extension theorem applies to the unbounded nonpolynomial function. -/
theorem exponentialReciprocal_extension :
    ∃ H : Free 2, graphRestriction coordinate H = exponentialReciprocal :=
  graphRestriction_surjective coordinate exponentialReciprocal

theorem empty_open : Subsingleton (Functions (0 : Free 1)) := by
  let : Subsingleton (Principal (0 : Free 1)) := zero_subsingleton
  exact (openEquiv (0 : Free 1)).symm.injective.subsingleton

theorem whole_open (g : Functions (1 : Free 1)) :
    ∃ H : Free 1, toOpen 1 (principalBase 1 H) = g := by
  refine ⟨oneRetraction (fromOpen 1 g),?_⟩
  have hi := congrArg (fun k : Hom (Principal (1 : Free 1)) (Principal (1 : Free 1)) => k (fromOpen 1 g)) one_inverse_base
  exact (congrArg (toOpen (1 : Free 1)) hi).trans
    (congrArg (fun k : Hom (Functions (1 : Free 1)) (Functions (1 : Free 1)) => k g) (toOpen_fromOpen 1))

/-- Restriction to x≠0 and g≠0 uses the proved product-localization comparison. -/
theorem restrict_reciprocal (g : Free 1) :
    toOpen (coordinate*g) (nestedMap coordinate g (fromOpen coordinate reciprocal)) =
      OpenFunctions.restrict (locus_product_subset coordinate g) reciprocal := by
  have h := congrArg (fun k : Hom (Principal coordinate) (Functions (coordinate*g)) => k (fromOpen coordinate reciprocal))
    (restriction_naturality coordinate g)
  have hi := congrArg (fun k : Hom (Functions coordinate) (Functions coordinate) => k reciprocal) (toOpen_fromOpen coordinate)
  change toOpen coordinate (fromOpen coordinate reciprocal) = reciprocal at hi
  change _ = OpenFunctions.restrict (locus_product_subset coordinate g) (toOpen coordinate (fromOpen coordinate reciprocal)) at h
  exact h.trans (congrArg (OpenFunctions.restrict (locus_product_subset coordinate g)) hi)

end Examples.SmoothLocalizationOpen
