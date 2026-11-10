import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Groupoid

/-! A functor of groupoids determines a genuinely functorial family of fibers
with selected base isomorphisms. Its total category recovers the domain. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidFiberDecomposition
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {E B : Type u} [Groupoid.{u} E] [Groupoid.{u} B] (P : E ⥤ B)

local instance (b : B) : IsGroupoid (CostructuredArrow P b) :=
  isGroupoid_of_reflects_iso (CostructuredArrow.proj P b)
local instance (b : B) : Groupoid (CostructuredArrow P b) := Groupoid.ofIsGroupoid

/-- A fiber object contains an actual domain object and a selected base arrow.
Its morphisms commute with those arrows; they need not be equalities. -/
def family : B ⥤ Grpd.{u,u} where
  obj b := Grpd.of (CostructuredArrow P b)
  map f := CostructuredArrow.map f
  map_id b := congrArg Cat.Hom.toFunctor ((CostructuredArrow.functor P).map_id b)
  map_comp f g := congrArg Cat.Hom.toFunctor ((CostructuredArrow.functor P).map_comp f g)

/-- This reuses Mathlib's costructured-arrow family without changing its maps. -/
theorem family_forget : family P ⋙ Grpd.forgetToCat = CostructuredArrow.functor P := rfl

abbrev Total := Grothendieck (family P ⋙ Grpd.forgetToCat)

def forget : Total P ⥤ E := CostructuredArrow.grothendieckProj P

instance : (forget P).Full where
  map_surjective {x y} g := by
    let b : x.base ⟶ y.base := inv x.fiber.hom ≫ P.map g ≫ y.fiber.hom
    let f : x ⟶ y := ⟨b, CostructuredArrow.homMk g (by
      change P.map g ≫ y.fiber.hom = x.fiber.hom ≫ b
      simp [b])⟩
    exact ⟨f, rfl⟩

instance : (forget P).Faithful where
  map_injective {x y} {f g} h := by
    have hf := CostructuredArrow.w f.fiber
    have hg := CostructuredArrow.w g.fiber
    change P.map f.fiber.left ≫ y.fiber.hom = x.fiber.hom ≫ f.base at hf
    change P.map g.fiber.left ≫ y.fiber.hom = x.fiber.hom ≫ g.base at hg
    change f.fiber.left = g.fiber.left at h
    have hb : f.base = g.base := by
      apply (cancel_epi x.fiber.hom).1
      rw [← hf, ← hg, h]
    apply Grothendieck.ext _ _ hb
    apply CostructuredArrow.ext
    change (eqToHom (show (CostructuredArrow.map g.base).obj x.fiber =
      (CostructuredArrow.map f.base).obj x.fiber by rw [hb])).left ≫
        f.fiber.left = g.fiber.left
    simpa only [CostructuredArrow.eqToHom_left, eqToHom_refl, Category.id_comp] using h

instance : (forget P).EssSurj where
  mem_essImage e := ⟨⟨P.obj e, CostructuredArrow.mk (𝟙 (P.obj e))⟩, ⟨Iso.refl _⟩⟩
instance : (forget P).IsEquivalence where

/-- The inverse and recovery isomorphisms are constructed from the explicit
fully faithful and essentially surjective projection. -/
def equivalence : Total P ≌ E := (forget P).asEquivalence

/-- The selected base arrows give the complete projection comparison. -/
def projectionComparison : forget P ⋙ P ≅ Grothendieck.forget (family P ⋙ Grpd.forgetToCat) :=
  NatIso.ofComponents (fun x => asIso x.fiber.hom) (by
    intro x y f
    exact CostructuredArrow.w f.fiber)

end SquareKit.Internal.PathTransport.GroupoidFiberDecomposition
