import SquareKit.AssemblySliceLift

/-! Generic multiplication in every assembly slice, independent of any
certificate state family or algebra. -/

universe u
namespace Realizability.Assembly

/-- Flatten partial values while retaining the total base coordinate. The
tracker is composed from the already constructed maps and multiplication. -/
def sliceMul {A B : Assembly.{u}} (p : Hom A B) :
    Hom (sliceLift (sliceBase p)) (sliceLift p) :=
  slicePack p (sliceBase (sliceBase p))
    (((sliceValue (sliceBase p)).comp (programLiftMap (sliceValue p))).comp (programLiftMul A))
    fun d x h => by
      change Option.join (Option.map (fun z : (sliceLift p).Carrier => z.val.2) d.val.2) = some x at h
      cases ho : d.val.2 with
      | none =>
        simp only [ho] at h
        change (none : Option A.Carrier) = some x at h
        cases h
      | some z =>
        simp only [ho] at h
        have hz : z.val.2 = some x := h
        exact (z.property x hz).trans (d.property z ho)

theorem sliceMul_base {A B : Assembly.{u}} (p : Hom A B) :
    (sliceMul p).comp (sliceBase p) = sliceBase (sliceBase p) := Hom.ext fun _ => rfl

open CategoryTheory

/-- The family-independent lifting monad on the standard slice category. -/
def sliceLiftMonad (B : Assembly.{u}) : Monad (Over B) where
  toFunctor := sliceLiftFunctor B
  η :=
    { app := fun X => Over.homMk (sliceUnit X.hom) (Hom.ext fun _ => rfl)
      naturality := fun X Y k => by
        apply Over.OverMorphism.ext
        apply Hom.ext
        intro x
        apply Subtype.ext
        exact Prod.ext (congrArg (fun h => h.toFun x) (Over.w k)) rfl }
  μ :=
    { app := fun X => Over.homMk (sliceMul X.hom) (sliceMul_base X.hom)
      naturality := fun X Y k => by
        apply Over.OverMorphism.ext
        apply Hom.ext
        rintro ⟨⟨b, t⟩, h⟩
        cases t with
        | none => rfl
        | some z =>
          rcases z with ⟨⟨b', s⟩, hs⟩
          cases s <;> rfl }
  assoc X := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rintro ⟨⟨b, t⟩, h⟩
    cases t with
    | none => rfl
    | some z =>
      rcases z with ⟨⟨b', s⟩, hs⟩
      cases s <;> rfl
  left_unit X := by
    apply Over.OverMorphism.ext
    exact Hom.ext fun _ => rfl
  right_unit X := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rintro ⟨⟨b, t⟩, h⟩
    cases t <;> rfl

end Realizability.Assembly
