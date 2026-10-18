import Applications.Orbifolds.Equivariant
import Applications.Diffeology.Manifolds
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Diffeology CategoryTheory MulAction
open scoped Manifold ContDiff

namespace Orbifolds
universe u
variable {G H : Type*} [Group G] [Group H] {X Y : Type u}
  [MulAction G X] [MulAction H Y] {φ : G ≃* H}

theorem orbitMap_smooth [DiffeologicalSpace X] [DiffeologicalSpace Y]
    (φ : G →* H) (f : X → Y) (he : ∀ g x, f (g • x) = φ g • f x)
    (hf : DSmooth f) : DSmooth (orbitMap φ f he) :=
  dSmooth_quotient_map hf _

/-- An invariant smooth observation descends smoothly to the orbit quotient. -/
theorem invariantLift_smooth [DiffeologicalSpace X] {Z : Type*} [DiffeologicalSpace Z]
    (f : X → Z) (hi : ∀ (g : G) x, f (g • x) = f x) (hf : DSmooth f) :
    DSmooth (invariantLift f hi) := dSmooth_quotient_lift hf _

/-- Smooth quotient comparison, independent of manifold presentations. -/
def CoordinateChange.smoothQuotient [DiffeologicalSpace X] [DiffeologicalSpace Y]
    (e : CoordinateChange φ X Y) (hf : DSmooth e.toEquiv) (hi : DSmooth e.toEquiv.symm) :
    SmoothEquiv (Quotient (orbitRel G X)) (Quotient (orbitRel H Y)) where
  toEquiv := e.quotientEquiv
  smooth := orbitMap_smooth φ.toMonoidHom _ e.equivariant hf
  smooth_symm := orbitMap_smooth φ.symm.toMonoidHom _ e.symm.equivariant hi

/-- A trivial action has the original diffeological space as its quotient,
regardless of how many elements the acting group has. -/
def trivialActionQuotient [DiffeologicalSpace X] (ht : ∀ (g : G) (x : X), g • x = x) :
    SmoothEquiv (Quotient (orbitRel G X)) X where
  toFun := Quotient.lift id (by
    intro a b h
    obtain ⟨g, hg⟩ := h
    exact hg.symm.trans (ht g b))
  invFun := Quotient.mk _
  left_inv q := Quotient.inductionOn q fun _ => rfl
  right_inv _ := rfl
  smooth := dSmooth_quotient_lift dSmooth_id _
  smooth_symm := dSmooth_quotient_mk _

theorem trivialAction_stabilizer (ht : ∀ (g : G) (x : X), g • x = x) (x : X) :
    stabilizer G x = ⊤ := by
  ext g
  simp [mem_stabilizer_iff, ht]

section Manifold
variable {E F A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace A] [TopologicalSpace B]
  {I : ModelWithCorners ℝ E A} {J : ModelWithCorners ℝ F B}
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace A X] [ChartedSpace B Y]
  [IsManifold I ∞ X] [IsManifold J ∞ Y]

/-- A conventional smooth equivariant coordinate change, with no assumed
conversion law between manifold and diffeological smoothness. -/
def manifoldCoordinateChange (f : Diffeomorph I J X Y ∞)
    (he : ∀ g x, f (g • x) = φ g • f x) : CoordinateChange φ X Y :=
  ⟨f.toEquiv, he⟩

/-- The quotient diffeomorphism consumes the proved manifold bridge. -/
def manifoldQuotient (f : Diffeomorph I J X Y ∞)
    (he : ∀ g x, f (g • x) = φ g • f x) :
    let _ := IsManifold.toDiffeology I X
    let _ := IsManifold.toDiffeology J Y
    SmoothEquiv (Quotient (orbitRel G X)) (Quotient (orbitRel H Y)) :=
  let _ := IsManifold.toDiffeology I X
  let _ := IsManifold.toDiffeology J Y
  (manifoldCoordinateChange f he).smoothQuotient f.contMDiff.dsmooth f.symm.contMDiff.dsmooth

omit [IsManifold I ∞ X] [IsManifold J ∞ Y] in
/-- Tangent intertwining in the ordinary manifold tangent bundles. The equation
includes the base point, so it applies away from fixed points as well. -/
theorem tangent_intertwining (f : X → Y) (he : ∀ g x, f (g • x) = φ g • f x)
    (hf : ContMDiff I J ∞ f) (g : G)
    (hg : ContMDiff I I ∞ (fun x : X => g • x))
    (hh : ContMDiff J J ∞ (fun y : Y => φ g • y)) :
    tangentMap I J f ∘ tangentMap I I (fun x : X => g • x) =
      tangentMap J J (fun y : Y => φ g • y) ∘ tangentMap I J f := by
  rw [← tangentMap_comp (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)),
    ← tangentMap_comp (hh.mdifferentiable (by simp)) (hf.mdifferentiable (by simp))]
  congr 1
  exact funext (he g)

end Manifold
end Orbifolds
