import Applications.Orbifolds.FiniteActionPresentation
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.Real.Lemmas

/-! Direct geometric controls for finite-action presentations. A trivial S3
action on the real line retains all its labels, including noncommuting ones.
The trivial-group real-line case is an externally proper diagonal; it asserts
nothing about unrestricted internal properness. -/
noncomputable section
open CategoryTheory Orbifolds.FiniteActionPresentation
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace Examples.FiniteActionPresentation

namespace Trivial
variable (G : Type*) [Group G]
local instance action : MulAction G ℝ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

variable [TopologicalSpace G] [DiscreteTopology G]

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem smooth (g : G) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => g • x) :=
  contMDiff_id

/-- The generic theorem applies on the whole real line, without compactness. -/
theorem presentation [Fintype G] [DecidableEq G] :
    IsProperMap (anchor (G := G) (M := ℝ)) ∧
    IsLocalDiffeomorph (arrowModel 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (source (G := G) (M := ℝ)) ∧
    IsLocalDiffeomorph (arrowModel 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (target (G := G) (M := ℝ)) :=
  proper_etale 𝓘(ℝ, ℝ) (smooth G)

example [Fintype G] : IsManifold (arrowModel 𝓘(ℝ, ℝ)) ∞ (G × ℝ) := inferInstance
example [Fintype G] : SecondCountableTopology (G × ℝ) := inferInstance
example [Fintype G] : T2Space (G × ℝ) := inferInstance

abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩

example : NoncompactSpace ℝ := inferInstance
def swap01 : S3 := Equiv.swap 0 1
def swap12 : S3 := Equiv.swap 1 2

/-- At every real point, distinct labels are distinct arrows with equal endpoints.
Properness is established for this same geometric action, not a separate disk. -/
theorem ineffective_noncompact (x : ℝ) :
    IsProperMap (anchor (G := S3) (M := ℝ)) ∧
    anchor (swap01, x) = anchor ((1 : S3), x) ∧
    (swap01, x) ≠ ((1 : S3), x) := by
  refine ⟨(presentation S3).1, rfl, ?_⟩
  intro h
  have h0 := congrArg (fun a : S3 × ℝ => a.1 0) h
  norm_num [swap01, Equiv.swap_apply_def] at h0

/-- The generic composable-pair coordinates realize first swap01, then swap12.
The reversed label fails even though both act trivially on the real base. -/
theorem noncommuting_composition (x : ℝ) :
    (composableEquiv (G := S3) (M := ℝ) ((swap01, swap12), x)).val =
      ((swap01, x), (swap12, x)) ∧
    compose swap01 swap12 x = (swap12 * swap01, x) ∧
    compose swap01 swap12 x ≠ (swap01 * swap12, x) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have h0 := congrArg (fun a : S3 × ℝ => a.1 0) h
  norm_num [compose, swap01, swap12, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h0

/-- The hom/fiber comparison retains the ineffective label in both directions. -/
theorem hom_roundtrips (x : ℝ)
    (f : (show ActionCategory S3 ℝ from x) ⟶ (show ActionCategory S3 ℝ from x))
    (a : {a : Arrow S3 ℝ // source a = x ∧ target a = x}) :
    (homEquiv (G := S3) x x).symm (homEquiv x x f) = f ∧
    homEquiv x x ((homEquiv (G := S3) x x).symm a) = a :=
  ⟨(homEquiv x x).symm_apply_apply f, (homEquiv x x).apply_symm_apply a⟩

/-- The external diagonal boundary already occurs for the trivial finite group.
This is deliberately not a theorem of unrestricted internal DPProper. -/
theorem diagonal :
    IsProperMap (anchor (G := PUnit) (M := ℝ)) ∧
    (∀ a : Arrow PUnit ℝ, anchor a = (a.2, a.2)) :=
  ⟨(presentation PUnit).1, fun _ => rfl⟩
/-- Removing the sole label gives the ordinary real-line diagonal map. -/
theorem diagonal_map : IsProperMap (fun x : ℝ => (x, x)) :=
  (presentation PUnit.{1}).1.comp (Homeomorph.punitProd ℝ).symm.isProperMap

end Trivial
end Examples.FiniteActionPresentation
