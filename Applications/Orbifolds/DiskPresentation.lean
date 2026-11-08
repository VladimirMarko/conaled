import Applications.Orbifolds.QuarterTurn
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Maps.Proper.Basic

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

def source (a : Arrow) : Disk := a.2
def target (a : Arrow) : Disk := a.1 • a.2
def unit (x : Disk) : Arrow := (1, x)
def inverse (a : Arrow) : Arrow := (a.1⁻¹, target a)
/-- Coordinates on the composable pairs: `g`, then `h`, based at `x`. -/
def compose (g h : C4) (x : Disk) : Arrow := (h * g, x)
def anchor (a : Arrow) : Disk × Disk := (source a, target a)

@[simp] theorem source_unit (x : Disk) : source (unit x) = x := rfl
@[simp] theorem target_unit (x : Disk) : target (unit x) = x := one_smul _ _
@[simp] theorem source_inverse (a : Arrow) : source (inverse a) = target a := rfl
@[simp] theorem target_inverse (a : Arrow) : target (inverse a) = source a := inv_smul_smul _ _
@[simp] theorem inverse_inverse (a : Arrow) : inverse (inverse a) = a := by
  ext <;> simp [inverse, target]
theorem target_compose (g h : C4) (x : Disk) :
    target (compose g h x) = h • (g • x) := mul_smul _ _ _

/-- Every fixed-label component has the whole disk as its source image. -/
def sourceChart (g : C4) : PartialDiffeomorph arrowModel 𝓘(ℝ, ℂ) Arrow Disk ∞ where
  toFun := source
  invFun x := (g, x)
  source := {a | a.1 = g}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := rfl
  left_inv' _a ha := Prod.ext ha.symm rfl
  right_inv' _ _ := rfl
  open_source := (isOpen_discrete {g}).preimage continuous_fst
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_snd.contMDiffOn
  contMDiffOn_invFun := (contMDiff_const.prodMk contMDiff_id).contMDiffOn

/-- Rotation and inverse rotation use the original action's smoothness proof. -/
def rotation (g : C4) : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Disk Disk ∞ where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  contMDiff_toFun := disk_action_smooth g
  contMDiff_invFun := disk_action_smooth g⁻¹

/-- The target chart on the component `g` rotates the source chart. -/
def targetChart (g : C4) : PartialDiffeomorph arrowModel 𝓘(ℝ, ℂ) Arrow Disk ∞ :=
  (sourceChart g).trans (rotation g).toPartialDiffeomorph

theorem source_etale : IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ source := by
  intro a
  exact ⟨sourceChart a.1, rfl, fun _ _ => rfl⟩

theorem target_etale : IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ target := by
  intro a
  refine ⟨targetChart a.1, ⟨rfl, Set.mem_univ _⟩, ?_⟩
  intro b hb
  change b.1 • b.2 = a.1 • b.2
  rw [hb.1]

/-- Compactness of the finite label space makes the source projection proper.
The Hausdorff disk product and continuity then give properness of the anchor. -/
theorem anchor_proper : IsProperMap anchor := by
  apply isProperMap_of_comp_of_t2
    (source_etale.contMDiff.continuous.prodMk target_etale.contMDiff.continuous)
    continuous_fst
  exact isProperMap_snd_of_compactSpace

theorem unit_smooth : ContMDiff 𝓘(ℝ, ℂ) arrowModel ∞ unit :=
  contMDiff_const.prodMk contMDiff_id

theorem inverse_smooth : ContMDiff arrowModel arrowModel ∞ inverse :=
  ((contMDiff_of_discreteTopology (I := 𝓘(ℝ, Fin 0 → ℝ))
    (I' := 𝓘(ℝ, Fin 0 → ℝ)) (f := fun g : C4 => g⁻¹)).comp
    contMDiff_fst).prodMk target_etale.contMDiff

/-- Composition is smooth in the coordinates `(g,h,x)` on composable pairs. -/
theorem compose_smooth :
    ContMDiff (((𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, ℂ))
      arrowModel ∞ (fun p : (C4 × C4) × Disk => compose p.1.1 p.1.2 p.2) :=
  ((contMDiff_of_discreteTopology
    (I := (𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Fin 0 → ℝ))
    (I' := 𝓘(ℝ, Fin 0 → ℝ)) (f := fun p : C4 × C4 => p.2 * p.1)).comp
    contMDiff_fst).prodMk contMDiff_snd

/-- These coordinates identify exactly the composable pairs, including their labels. -/
def composableEquiv : (C4 × C4) × Disk ≃
    {p : Arrow × Arrow // target p.1 = source p.2} where
  toFun p := ⟨((p.1.1, p.2), (p.1.2, p.1.1 • p.2)), rfl⟩
  invFun p := ((p.val.1.1, p.val.2.1), p.val.1.2)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext rfl p.property)

/-- Coordinate arrows are the arrows of Mathlib's existing action groupoid. -/
def asHom (a : Arrow) :
    (show CategoryTheory.ActionCategory C4 Disk from source a) ⟶
      (show CategoryTheory.ActionCategory C4 Disk from target a) :=
  CategoryTheory.Functor.Elements.homMk a.1 rfl

/-- Every categorical arrow has these coordinates, with its source remembered. -/
def ofHom {x y : ActionCategory C4 Disk} (f : x ⟶ y) : Arrow := (f.hom, x.back)

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
      {a : Arrow // source a = x ∧ target a = y} where
  toFun f := ⟨ofHom f, rfl, f.map_val⟩
  invFun a := Functor.Elements.homMk a.val.1 (by
    change a.val.1 • x = y
    exact (congrArg (fun z => a.val.1 • z) a.property.1.symm).trans a.property.2)
  left_inv _ := Functor.Elements.Hom.ext rfl
  right_inv a := by
    apply Subtype.ext
    exact Prod.ext rfl a.property.1.symm

/-- The actual open-disk presentation is proper and étale. -/
theorem proper_etale : IsProperMap anchor ∧
    IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ source ∧
    IsLocalDiffeomorph arrowModel 𝓘(ℝ, ℂ) ∞ target :=
  ⟨anchor_proper, source_etale, target_etale⟩

end Orbifolds.QuarterTurn.DiskPresentation
