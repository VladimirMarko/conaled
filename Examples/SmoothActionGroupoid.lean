import SquareKit.SmoothActionGroupoid
import Examples.SmoothManifoldAction
import Examples.SmoothTorsors

/-! A proper étale ineffective line groupoid and noncommutative operation controls. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace Examples.SmoothActionGroupoid
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothOpenSite
open Orbifolds.QuarterTurn
attribute [local instance] SmoothManifoldAction.trivial
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩

abbrev Arrow := SquareKit.SmoothActionGroupoid.ArrowModel (d := 1) (G := C4) (M := Space 1)
abbrev presentation := SquareKit.SmoothActionGroupoid.groupoid (SmoothManifoldAction.smooth C4)

/-- The same noncompact geometric arrows used by the interpreted presentation are proper étale. -/
theorem proper_etale :
    IsProperMap (fun a : Arrow =>
      (SquareKit.SmoothActionGroupoid.source a,SquareKit.SmoothActionGroupoid.target a)) ∧
    IsLocalDiffeomorph (modelWithCorners 1) (modelWithCorners 1) ∞
      (SquareKit.SmoothActionGroupoid.source (d := 1) (G := C4) (M := Space 1)) ∧
    IsLocalDiffeomorph (modelWithCorners 1) (modelWithCorners 1) ∞
      (SquareKit.SmoothActionGroupoid.target (d := 1) (G := C4) (M := Space 1)) :=
  SquareKit.SmoothActionGroupoid.proper_etale (SmoothManifoldAction.smooth C4)

example : NoncompactSpace (Space 1) := inferInstance

def arrowSheet (g : C4) : object 1 (Space 1) ⟶ presentation.arrows :=
  map (SquareKit.SmoothActionGroupoid.sheet (d := 1) (M := Space 1) g)
    (SquareKit.SmoothActionGroupoid.sheet_smooth (d := 1) (M := Space 1) g)

/-- Nonidentity isotropy remains a distinct actual geometric sheaf map. -/
theorem ineffective_distinct : arrowSheet quarterTurn ≠ arrowSheet 1 := by
  intro h
  have he := map_injective _ _ h
  have hg := congrArg (fun f => (f (0 : Space 1)).1) he
  exact SmoothTorsors.quarterTurn_ne_one hg

/-- Both endpoints agree even though the two maps above differ. -/
theorem ineffective_endpoints (g : C4) :
    arrowSheet g ≫ presentation.source = 𝟙 _ ∧ arrowSheet g ≫ presentation.target = 𝟙 _ := by
  constructor
  · rw [SquareKit.SmoothActionGroupoid.groupoid_source, arrowSheet, ← map_comp]
    exact map_id
  · rw [SquareKit.SmoothActionGroupoid.groupoid_target, arrowSheet, ← map_comp]
    exact map_id

/-- The unit and inverse in the public presentation are actual smooth maps. -/
theorem interpreted_operations :
    presentation.unit = SquareKit.SmoothActionGroupoid.unitMap (d := 1) (G := C4) (M := Space 1) ∧
    presentation.inverse = SquareKit.SmoothActionGroupoid.inverseMap (SmoothManifoldAction.smooth C4) :=
  ⟨SquareKit.SmoothActionGroupoid.groupoid_unit _, SquareKit.SmoothActionGroupoid.groupoid_inverse _⟩

/-- The action coordinates recover every actual arrow over every sheaf parameter. -/
def allParameterArrowEquiv (X : Sheaf topology Type) :
    (X ⟶ presentation.arrows) ≃
      (X ⟶ SheafRelation.product (locallyConstantGroupSheaf C4) (object 1 (Space 1))) :=
  (SquareKit.SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)).homToEquiv

/-- A locally varying label stays varying after conversion to actual geometric arrows. -/
theorem varying_not_constant (m : SmoothTorsors.disconnected ⟶ object 1 (Space 1)) (g : C4) :
    SheafRelation.lift SmoothTorsors.varyingLabel m ≫
        (SquareKit.SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)).inv ≠
      SheafRelation.lift (constantSection SmoothTorsors.disconnected g) m ≫
        (SquareKit.SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)).inv := by
  intro h
  have he := (cancel_mono
    (SquareKit.SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)).inv).mp h
  exact SmoothTorsors.varyingLabel_not_constant g
    (by simpa using congrArg (fun k : SmoothTorsors.disconnected ⟶
      SheafRelation.product (locallyConstantGroupSheaf C4) (object 1 (Space 1)) =>
      k ≫ SheafRelation.fst _ _) he)

/-- A concrete object over the disconnected test parameter, with value zero on both pieces. -/
def disconnectedZero : SmoothTorsors.disconnected ⟶ object 1 (Space 1) :=
  let z : SmoothTorsors.point ⟶ object 1 (Space 1) :=
    (sheafYonedaEquiv (SmoothPresentationSite.free 0) _).symm
      ((SquareKit.SmoothManifoldAction.pointEquiv (d := 1) (M := Space 1)).symm 0)
  Limits.coprod.desc z z

/-- The chosen ineffective example admits actual arrows with no single constant label. -/
theorem concrete_varying_arrows (g : C4) :
    SheafRelation.lift SmoothTorsors.varyingLabel disconnectedZero ≫
        (SquareKit.SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)).inv ≠
      SheafRelation.lift (constantSection SmoothTorsors.disconnected g) disconnectedZero ≫
        (SquareKit.SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)).inv :=
  varying_not_constant disconnectedZero g

section Noncommutative
abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩

/-- The checked public multiplication uses `h * g`, not `g * h`. -/
theorem noncommuting_composition :
    letI := SquareKit.SmoothActionGroupoid.composableCharts (SmoothManifoldAction.smooth S3)
    letI := SquareKit.SmoothActionGroupoid.composableManifold (SmoothManifoldAction.smooth S3)
    let g := SmoothManifoldAction.g
    let h := SmoothManifoldAction.h
    map (SquareKit.SmoothActionGroupoid.composableSheet (d := 1) (M := Space 1) g h)
      (SquareKit.SmoothActionGroupoid.composableSheet_smooth (SmoothManifoldAction.smooth S3) g h) ≫
      (SquareKit.SmoothActionGroupoid.groupoid_composable_isPullback
        (SmoothManifoldAction.smooth S3)).isoPullback.hom ≫
      (SquareKit.SmoothActionGroupoid.groupoid (SmoothManifoldAction.smooth S3)).comp ≠
    map (SquareKit.SmoothActionGroupoid.sheet (d := 1) (M := Space 1) (g*h))
      (SquareKit.SmoothActionGroupoid.sheet_smooth (d := 1) (M := Space 1) (g*h)) := by
  let := SquareKit.SmoothActionGroupoid.composableCharts (SmoothManifoldAction.smooth S3)
  let := SquareKit.SmoothActionGroupoid.composableManifold (SmoothManifoldAction.smooth S3)
  dsimp only
  rw [SquareKit.SmoothActionGroupoid.groupoid_compose_sheets]
  intro h
  have he := congrArg (fun f => ((f (0 : Space 1)).1 : S3) 0) (map_injective _ _ h)
  norm_num [SquareKit.SmoothActionGroupoid.sheet, SmoothManifoldAction.g,
    SmoothManifoldAction.h, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at he

end Noncommutative
end Examples.SmoothActionGroupoid
