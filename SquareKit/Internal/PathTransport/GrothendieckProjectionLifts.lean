import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Groupoid

/-! The actual Grothendieck projection supplies the base lifts used by the
fiberwise full and essentially-surjective criteria. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GrothendieckProjectionLifts
open CategoryTheory
universe u v w z
variable {C : Type u} [Groupoid.{v} C] (F : C ⥤ Cat.{w,z})

/-- Lifting keeps the requested base arrow exactly. -/
theorem lift_base (x y : Grothendieck F) (b : x.base ⟶ y.base) :
    ∃ (t : Grothendieck F) (e : x ≅ t) (h : t.base = y.base),
      e.hom.base ≫ eqToHom h = b := by
  refine ⟨x.transport b, (x.transportIso (asIso b)).symm, rfl, ?_⟩
  change b ≫ 𝟙 _ = b
  exact Category.comp_id b

/-- A chosen base isomorphism moves any target object into its requested fiber. -/
theorem lift_iso (x : Grothendieck F) (c : C) (e : Nonempty (x.base ≅ c)) :
    ∃ t : Grothendieck F, t.base = c ∧ Nonempty (x ≅ t) := by
  obtain ⟨e⟩ := e
  exact ⟨x.transport e.hom, rfl, ⟨(x.transportIso e).symm⟩⟩

end SquareKit.Internal.PathTransport.GrothendieckProjectionLifts
