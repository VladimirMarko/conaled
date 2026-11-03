import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Experimental analytic gluing for finite-dimensional smooth functions.
The partition of unity supplies actual global functions from local convex constraints. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace SquareKit.SmoothLocalGluing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Pointwise convex constraints can be glued without bounds or compact support
on the desired function. Local candidates need only be smooth on their neighborhoods. -/
theorem convex_constraints (t : E → Set ℝ) (ht : ∀ x, Convex ℝ (t x))
    (hl : ∀ x, ∃ U ∈ 𝓝 x, ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ x, g x ∈ t x := by
  obtain ⟨g,hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (𝓘(ℝ,E)) ht
    (fun x => by
      obtain ⟨U,hU,g,hgs,hgt⟩ := hl x
      exact ⟨U,hU,g,hgs.contMDiffOn,hgt⟩)
  exact ⟨g,g.contMDiff.contDiff,hg⟩

/-- Extend a function from an open neighborhood of a closed set, preserving its
values on that closed set. The closed set need not be compact. -/
theorem closed_extension (S W : Set E) (hS : IsClosed S) (hW : IsOpen W) (hSW : S ⊆ W)
    (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g W) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧ ∀ x ∈ S, q x = g x := by
  let t : E → Set ℝ := fun x => {r | x ∈ S → r = g x}
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x a ha b hb c d hc hd hcd hx
    change c*a+d*b = g x
    rw [ha hx,hb hx,← add_mul,hcd,one_mul]
  obtain ⟨q,hq,hqt⟩ := convex_constraints t ht (fun x => by
    by_cases hx : x ∈ S
    · exact ⟨W,hW.mem_nhds (hSW hx),g,hg,fun _ _ _ => rfl⟩
    · exact ⟨Sᶜ,hS.isOpen_compl.mem_nhds hx,fun _ => 0,contDiffOn_const,
        fun y hy hys => (hy hys).elim⟩)
  exact ⟨q,hq,hqt⟩

/-- Local solutions of a scalar linear equation glue to a global smooth solution. -/
theorem scalar_equation (a b : E → ℝ)
    (hl : ∀ x, ∃ U ∈ 𝓝 x, ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ U, a y * g y = b y) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ x, a x * g x = b x := by
  apply convex_constraints (fun x => {r | a x * r = b x}) _ hl
  intro x u hu v hv c d hc hd hcd
  change a x * (c*u+d*v) = b x
  calc
    _ = c*(a x*u)+d*(a x*v) := by ring
    _ = b x := by rw [hu,hv,← add_mul,hcd,one_mul]

end SquareKit.SmoothLocalGluing
