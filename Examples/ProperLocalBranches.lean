import Examples.FiniteActionPresentation
import Applications.Orbifolds.ProperLocalBranches
import Applications.Orbifolds.LocalBranchRestriction
import Applications.Orbifolds.DiskPresentation

/-! Ordinary controls for local branch diagrams of proper anchors. -/
noncomputable section
open scoped Manifold ContDiff
namespace Examples.ProperLocalBranches

open TopologicalSpace Orbifolds.LocalBranches

/-- A unit presentation has one branch on the intersection of the endpoint windows. -/
def unitDiagram {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (U V : Opens M) :
    Diagram I I (id : M → M) id U V Unit where
  piece _ := U ⊓ V
  domain _ := U ⊓ V
  sourceEquiv _ := Diffeomorph.refl I ↥(U ⊓ V : Opens M) ∞
  source_eq _ _ := rfl
  domain_le _ := inf_le_left
  target_mem _ a := a.property.2
  disjoint := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  covers a := by simp

@[simp] theorem unitDiagram_assemble {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (U V : Opens M) (x : (U ⊓ V : Opens M)) :
    ((unitDiagram I U V).assemble () x).val = x.val := rfl

/-- A graph over its source is proper even when its target map is constant. -/
theorem constant_anchor_proper : IsProperMap (fun x : ℝ => (x, (0 : ℝ))) := by
  apply isProperMap_of_comp_of_t2 (continuous_id.prodMk continuous_const) continuous_fst
  exact isProperMap_id

theorem identity_source_etale : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (id : ℝ → ℝ) :=
  (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph

/-- This primary-theorem input cannot satisfy the stronger target-étale premise. -/
theorem constant_target_not_etale :
    ¬ IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ => (0 : ℝ)) := by
  intro h
  have ho := h.isOpenMap Set.univ isOpen_univ
  have he : (fun _ : ℝ => (0 : ℝ)) '' Set.univ = {0} := by
    ext x
    simp
  rw [he] at ho
  exact not_isOpen_singleton (0 : ℝ) ho

/-- The unequal endpoints of the real-line unit presentation have no arrows. -/
theorem diagonal_fiber_empty (x y : ℝ) (hxy : x ≠ y) :
    IsEmpty {a : ℝ // a = x ∧ a = y} :=
  ⟨fun a => hxy (a.property.1.symm.trans a.property.2)⟩

/-- The primary construction applies when the smooth target is not étale. -/
theorem constant_target_branches (x y : ℝ) :
    ∃ U V : Opens ℝ, x ∈ U ∧ y ∈ V ∧
      Nonempty (Diagram 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ)
        (fun _ => (0 : ℝ)) U V {a : ℝ // a = x ∧ (0 : ℝ) = y}) :=
  exists_diagram (IY := 𝓘(ℝ, ℝ)) identity_source_etale contMDiff_const constant_anchor_proper x y

/-- The proper unit anchor supplies an empty whole rectangle at unequal endpoints. -/
theorem diagonal_empty_branches (x y : ℝ) (hxy : x ≠ y) :
    ∃ U V : Opens ℝ, x ∈ U ∧ y ∈ V ∧
      ∃ D : Diagram 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) id U V
        {a : ℝ // a = x ∧ a = y}, D.region = ⊥ :=
  exists_empty_diagram (IY := 𝓘(ℝ, ℝ)) identity_source_etale contMDiff_id
    Examples.FiniteActionPresentation.Trivial.diagonal_map x y
    (fun _ h => hxy (h.1.symm.trans h.2))

def wide : Opens ℝ := ⟨Set.Ioo (-2) 2, isOpen_Ioo⟩
def narrow : Opens ℝ := ⟨Set.Ioo (-1) 1, isOpen_Ioo⟩
theorem narrow_le_wide : narrow ≤ wide := by
  intro x hx
  change -1 < x ∧ x < 1 at hx
  change -2 < x ∧ x < 2
  constructor <;> linarith [hx.1,hx.2]

def restrictedUnit := (unitDiagram 𝓘(ℝ, ℝ) wide wide).restrict
  contMDiff_id contMDiff_id wide narrow le_rfl narrow_le_wide

/-- Restricting the target window cuts down the actual source domain. -/
theorem restrictedUnit_domain : restrictedUnit.domain () = narrow := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha.2.2
  · intro hx
    exact ⟨x,⟨⟨narrow_le_wide hx,narrow_le_wide hx⟩,narrow_le_wide hx,hx⟩,rfl⟩

theorem restrictedUnit_domain_nonempty : Set.Nonempty (restrictedUnit.domain () : Set ℝ) := by
  rw [restrictedUnit_domain]
  exact ⟨0, by norm_num [narrow]⟩

theorem restrictedUnit_domain_proper : restrictedUnit.domain () < wide := by
  rw [restrictedUnit_domain]
  refine lt_of_le_of_ne narrow_le_wide ?_
  intro he
  have hm : (3/2 : ℝ) ∈ wide := by norm_num [wide]
  rw [← he] at hm
  norm_num [narrow] at hm

/-- Endpoint recovery uses the public fiber equivalence of the restricted diagram. -/
theorem restrictedUnit_fiber_roundtrip
    (x : wide) (y : narrow) (a : {a : ℝ // a = x.val ∧ a = y.val}) :
    (restrictedUnit.fiberEquiv x y).symm (restrictedUnit.fiberEquiv x y a) = a :=
  (restrictedUnit.fiberEquiv x y).symm_apply_apply a

section FiniteAction
open Orbifolds.FiniteActionPresentation
open scoped Orbifolds.FiniteActionPresentation
variable {G M E H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [Fintype G] [DecidableEq G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [MulAction G M] [T2Space M] [SecondCountableTopology M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  (smoothAction : ∀ g : G, ContMDiff I I ∞ (fun x : M => g • x))

include smoothAction in
/-- Finite actions use the primary proper-anchor construction with their product arrow model. -/
theorem finite_action_branches (x y : M) :
    ∃ U V : Opens M, x ∈ U ∧ y ∈ V ∧
      Nonempty (Diagram (arrowModel I) I (source (G := G) (M := M)) target U V
        {a : Arrow G M // source a = x ∧ target a = y}) := by
  have hp := proper_etale I smoothAction
  exact exists_diagram hp.2.1 hp.2.2.contMDiff hp.1 x y

/-- Explicit finite-action windows use the same public chart constructor. -/
def finiteActionDiagram (U V : Opens M) :
    Diagram (arrowModel I) I (source (G := G) (M := M)) target U V G :=
  diagramOfCharts (fun g => sourceChart I g) (fun _ _ _ => rfl)
    (by
      intro g h hgh
      apply Set.disjoint_left.mpr
      intro a ha hb
      exact hgh (ha.symm.trans hb))
    (source_etale I).contMDiff (target_etale I smoothAction).contMDiff U V
    (fun a _ _ => ⟨a.1,rfl⟩)

omit [Fintype G] [DecidableEq G] [T2Space M] [SecondCountableTopology M] [IsManifold I ∞ M] in
@[simp] theorem finiteActionDiagram_assemble (U V : Opens M) (g : G)
    (x : (finiteActionDiagram I smoothAction U V).domain g) :
    ((finiteActionDiagram I smoothAction U V).assemble g x).val = (g,x.val) := rfl

omit [Fintype G] [DecidableEq G] [T2Space M] [SecondCountableTopology M] [IsManifold I ∞ M] in
/-- The explicit diagram retains its source and target equations on each label. -/
theorem finiteActionDiagram_branch (U V : Opens M) (g : G)
    (x : (finiteActionDiagram I smoothAction U V).domain g) :
    ((finiteActionDiagram I smoothAction U V).branch g x).val = g • x.val := rfl

end FiniteAction

namespace Ineffective
open Orbifolds.FiniteActionPresentation
open scoped Orbifolds.FiniteActionPresentation
abbrev S3 := Examples.FiniteActionPresentation.Trivial.S3
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩
local instance : MulAction S3 ℝ := Examples.FiniteActionPresentation.Trivial.action S3

/-- The new proper-anchor theorem applies to the existing ineffective noncompact action. -/
theorem branches (x : ℝ) :
    ∃ U V : Opens ℝ, x ∈ U ∧ x ∈ V ∧
      Nonempty (Diagram (arrowModel 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (source (G := S3) (M := ℝ)) target U V
        {a : Arrow S3 ℝ // source a = x ∧ target a = x}) :=
  finite_action_branches 𝓘(ℝ, ℝ) (Examples.FiniteActionPresentation.Trivial.smooth S3) x x

/-- Every constructed diagram distinguishes ineffective labels in the actual endpoint fiber. -/
theorem fiber_labels_distinct {U V : Opens ℝ} {J : Type*}
    (D : Diagram (arrowModel 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (source (G := S3) (M := ℝ)) target U V J)
    (x : ℝ) (hx : x ∈ U) (hy : x ∈ V) :
    D.fiberEquiv ⟨x,hx⟩ ⟨x,hy⟩ ⟨(Examples.FiniteActionPresentation.Trivial.swap01,x),rfl,rfl⟩ ≠
      D.fiberEquiv ⟨x,hx⟩ ⟨x,hy⟩ ⟨(1,x),rfl,rfl⟩ := by
  intro h
  have ha := congrArg Subtype.val ((D.fiberEquiv ⟨x,hx⟩ ⟨x,hy⟩).injective h)
  exact (Examples.FiniteActionPresentation.Trivial.ineffective_noncompact x).2.2 ha

end Ineffective

namespace Disk
open Orbifolds.QuarterTurn Orbifolds.QuarterTurn.DiskPresentation

/-- The existing disk presentation supplies the properness and smooth charts directly. -/
theorem branches (x y : Orbifolds.QuarterTurn.Disk) :
    ∃ U V : Opens Orbifolds.QuarterTurn.Disk, x ∈ U ∧ y ∈ V ∧
      ∃ D : Diagram arrowModel 𝓘(ℝ, ℂ) source target U V
        {a : Arrow // source a = x ∧ target a = y}, Nonempty (Bisections D 𝓘(ℝ, ℂ)) :=
  exists_bisection_diagram source_etale target_etale anchor_proper x y

/-- The retained disk arrows, including their labels, survive both directions. -/
theorem fiber_roundtrip {U V : Opens Orbifolds.QuarterTurn.Disk} {J : Type*}
    (D : Diagram arrowModel 𝓘(ℝ, ℂ) source target U V J)
    (x : U) (y : V) (a : {a : Arrow // source a = x.val ∧ target a = y.val}) :
    (D.fiberEquiv x y).symm (D.fiberEquiv x y a) = a :=
  (D.fiberEquiv x y).symm_apply_apply a
end Disk

end Examples.ProperLocalBranches
