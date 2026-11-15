import Applications.Orbifolds.QuarterTurn
import Applications.Orbifolds.FiniteActionPresentation

/-! The external action presentation of the open disk. An arrow `(g,x)` goes
from `x` to `g • x`; following it by `(h,g • x)` gives `(h*g,x)`.
Proper means Mathlib's `IsProperMap` (Bourbaki properness). -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace Orbifolds.QuarterTurn.DiskPresentation

instance labelCharts : ChartedSpace (Fin 0 → ℝ) C4 := ChartedSpace.ofDiscreteTopology
instance labelManifold : IsManifold 𝓘(ℝ, Fin 0 → ℝ) ∞ C4 :=
  IsManifold.of_discreteTopology ∞

abbrev Arrow := C4 × Disk
abbrev arrowModel := (𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, ℂ)

def source (a : Arrow) : Disk :=
  FiniteActionPresentation.source a
def target (a : Arrow) : Disk :=
  FiniteActionPresentation.target a
def unit (x : Disk) : Arrow :=
  FiniteActionPresentation.unit x
def inverse (a : Arrow) : Arrow :=
  FiniteActionPresentation.inverse a
/-- Coordinates on the composable pairs: `g`, then `h`, based at `x`. -/
def compose (g h : C4) (x : Disk) : Arrow :=
  FiniteActionPresentation.compose g h x
def anchor (a : Arrow) : Disk × Disk :=
  FiniteActionPresentation.anchor a

@[simp] theorem source_unit (x : Disk) : source (unit x) = x := rfl
@[simp] theorem target_unit (x : Disk) : target (unit x) = x := one_smul _ _
@[simp] theorem source_inverse (a : Arrow) : source (inverse a) = target a := rfl
@[simp] theorem target_inverse (a : Arrow) : target (inverse a) = source a := inv_smul_smul _ _
@[simp] theorem inverse_inverse (a : Arrow) : inverse (inverse a) = a := by
  exact FiniteActionPresentation.inverse_inverse a
theorem target_compose (g h : C4) (x : Disk) :
    target (compose g h x) = h • (g • x) := mul_smul _ _ _

/-- Every fixed-label component has the whole disk as its source image. -/
def sourceChart (g : C4) : PartialDiffeomorph arrowModel 𝓘(ℝ, ℂ) Arrow Disk ∞ :=
  FiniteActionPresentation.sourceChart 𝓘(ℝ, ℂ) g

/-- Rotation and inverse rotation use the original action's smoothness proof. -/
def rotation (g : C4) : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Disk Disk ∞ :=
  FiniteActionPresentation.actionDiffeomorph 𝓘(ℝ, ℂ) disk_action_smooth g

/-- The target chart on the component `g` rotates the source chart. -/
def targetChart (g : C4) : PartialDiffeomorph arrowModel 𝓘(ℝ, ℂ) Arrow Disk ∞ :=
  FiniteActionPresentation.targetChart 𝓘(ℝ, ℂ) disk_action_smooth g

theorem source_etale : IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ source :=
  FiniteActionPresentation.source_etale 𝓘(ℝ, ℂ)

theorem target_etale : IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ target :=
  FiniteActionPresentation.target_etale 𝓘(ℝ, ℂ) disk_action_smooth

/-- Compactness of the finite label space makes the source projection proper.
The Hausdorff disk product and continuity then give properness of the anchor. -/
theorem anchor_proper : IsProperMap anchor :=
  FiniteActionPresentation.anchor_proper_of_compact
    target_etale.contMDiff.continuous

theorem unit_smooth : ContMDiff 𝓘(ℝ, ℂ) arrowModel ∞ unit :=
  FiniteActionPresentation.unit_smooth 𝓘(ℝ, ℂ)

theorem inverse_smooth : ContMDiff arrowModel arrowModel ∞ inverse :=
  FiniteActionPresentation.inverse_smooth 𝓘(ℝ, ℂ) disk_action_smooth

/-- Composition is smooth in the coordinates `(g,h,x)` on composable pairs. -/
theorem compose_smooth :
    ContMDiff (((𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, ℂ))
      arrowModel ∞ (fun p : (C4 × C4) × Disk => compose p.1.1 p.1.2 p.2) :=
  FiniteActionPresentation.compose_smooth 𝓘(ℝ, ℂ)

/-- These coordinates identify exactly the composable pairs, including their labels. -/
def composableEquiv : (C4 × C4) × Disk ≃
    {p : Arrow × Arrow // target p.1 = source p.2} :=
  FiniteActionPresentation.composableEquiv

/-- Coordinate arrows are the arrows of Mathlib's existing action groupoid. -/
def asHom (a : Arrow) :
    (show CategoryTheory.ActionCategory C4 Disk from source a) ⟶
      (show CategoryTheory.ActionCategory C4 Disk from target a) :=
  FiniteActionPresentation.asHom a

/-- Every categorical arrow has these coordinates, with its source remembered. -/
def ofHom {x y : ActionCategory C4 Disk} (f : x ⟶ y) : Arrow :=
  FiniteActionPresentation.ofHom f

@[simp] theorem ofHom_ident (x : ActionCategory C4 Disk) : ofHom (𝟙 x) = unit x.back := rfl

theorem ofHom_comp {x y z : ActionCategory C4 Disk} (f : x ⟶ y) (g : y ⟶ z) :
    ofHom (f ≫ g) = compose f.hom g.hom x.back := rfl

theorem ofHom_inverse {x y : ActionCategory C4 Disk} (f : x ⟶ y) :
    ofHom (Groupoid.inv f) = inverse (ofHom f) := by
  change ((show C4 from f.hom)⁻¹, y.back) = ((show C4 from f.hom)⁻¹, (show C4 from f.hom) • x.back)
  exact Prod.ext rfl f.map_val.symm

/-- The fiber of the geometric anchor is the existing category's hom type. -/
def homEquiv (x y : Disk) :
    ((show ActionCategory C4 Disk from x) ⟶ (show ActionCategory C4 Disk from y)) ≃
      {a : Arrow // source a = x ∧ target a = y} :=
  FiniteActionPresentation.homEquiv x y

/-- Explicit enumeration for the analytic root-of-unity label type. -/
@[instance_reducible] def labelFintype : Fintype C4 := Fintype.ofFinite C4

/-- The actual open-disk presentation is proper and étale. -/
theorem proper_etale : IsProperMap anchor ∧
    IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ source ∧
    IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ target := by
  classical
  let := labelFintype
  exact FiniteActionPresentation.proper_etale 𝓘(ℝ, ℂ) disk_action_smooth

end Orbifolds.QuarterTurn.DiskPresentation
