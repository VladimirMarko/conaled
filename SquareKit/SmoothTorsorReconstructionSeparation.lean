import SquareKit.SmoothTorsorReconstruction
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Instances.Discrete

/-! Separation and countability consequences for the fiber-bundle topology.
The results apply after the point-fiber prebundle has constructed that topology. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTorsorReconstruction

open Bundle Set Topology TopologicalSpace
variable {B : Type*} (F : Type*) (E : B → Type*)
  [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/-- Distinct base points are separated in the base; points over the same base
point are separated inside a common trivialization. -/
theorem fiberBundle_t2Space [T2Space B] [T2Space F] : T2Space (TotalSpace F E) := by
  constructor
  intro x y hxy
  by_cases h : x.proj = y.proj
  · let e := trivializationAt F E x.proj
    have hx : x ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr (h ▸ mem_baseSet_trivializationAt F E x.proj)
    let : T2Space e.source := e.toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm.t2Space
    exact separated_by_isOpenEmbedding e.open_source.isOpenEmbedding_subtypeVal
      (show (⟨x, hx⟩ : e.source) ≠ ⟨y, hy⟩ from fun he => hxy (congrArg Subtype.val he))
  · exact separated_by_continuous (FiberBundle.continuous_proj F E) h

/-- A countable subcover of base trivializations gives a countable cover of
second-countable open subsets of the total space. -/
theorem fiberBundle_secondCountableTopology [SecondCountableTopology B]
    [SecondCountableTopology F] : SecondCountableTopology (TotalSpace F E) := by
  obtain ⟨s, hs, hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun b : B => (trivializationAt F E b).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E b))
  let : Countable s := hs.to_subtype
  let U : s → Set (TotalSpace F E) := fun b => (trivializationAt F E b.val).source
  let : ∀ b : s, SecondCountableTopology (U b) := fun b =>
    (trivializationAt F E b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U)
    (fun b => (trivializationAt F E b.val).open_source)
  apply eq_univ_of_forall
  intro z
  have hz : z.proj ∈ ⋃ b ∈ s, (trivializationAt F E b).baseSet := hcover.symm ▸ mem_univ _
  obtain ⟨b, hb, hz⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion.mpr ⟨⟨b, hb⟩, (trivializationAt F E b).mem_source.mpr hz⟩

/-- Discrete fibers impose no cardinality restriction on Hausdorffness. -/
theorem fiberBundle_t2Space_of_discrete [T2Space B] [DiscreteTopology F] :
    T2Space (TotalSpace F E) :=
  fiberBundle_t2Space F E

/-- Countable discrete fibers suffice; finite fibers are a specialization. -/
theorem fiberBundle_secondCountableTopology_of_countable_discrete
    [SecondCountableTopology B] [DiscreteTopology F] [Countable F] :
    SecondCountableTopology (TotalSpace F E) :=
  fiberBundle_secondCountableTopology F E

end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open ManifoldRealization SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (Model n) ∞ B]
  [TopologicalSpace G] [DiscreteTopology G]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))

/-- Hausdorffness is a consequence of the base hypothesis, not an admission condition. -/
theorem total_t2Space [T2Space B] : T2Space (Total P) :=
  fiberBundle_t2Space_of_discrete G (Fiber P)

/-- Countable discrete groups suffice; in particular this applies to finite groups. -/
theorem total_secondCountableTopology [SecondCountableTopology B] [Countable G] :
    SecondCountableTopology (Total P) :=
  fiberBundle_secondCountableTopology_of_countable_discrete G (Fiber P)
end SquareKit.SmoothTorsorReconstruction
