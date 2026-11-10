import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence

/-! A family of total matching data with fixed base lands in the explicit fiber. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {Z : Type v} [Category.{u} Z]
variable (E : Z ⥤ Datum (A.total h).toDiagram) (d : Datum D.toDiagram)
variable (he : E ⋙ (A.projection h).functor = (Functor.const Z).obj d)

def fixedBaseObject (z : Z) : Fiber A h d :=
  Fiber.ofDatum (E.obj z) (Functor.congr_obj he z)

def fixedBaseArrow {x y : Z} (f : x ⟶ y) :
    fixedBaseObject A h E d he x ⟶ fixedBaseObject A h E d he y where
  matchingArrow := eqToHom (Fiber.datum_ofDatum (E.obj x) (Functor.congr_obj he x)) ≫
    E.map f ≫ eqToHom (Fiber.datum_ofDatum (E.obj y) (Functor.congr_obj he y)).symm
  vertical := by
    let P := (A.projection h).functor ⋙ Datum.localFunctor
    change P.map (eqToHom (Fiber.datum_ofDatum (E.obj x) (Functor.congr_obj he x)) ≫
      E.map f ≫ eqToHom (Fiber.datum_ofDatum (E.obj y) (Functor.congr_obj he y)).symm) = _
    rw [Functor.map_comp, Functor.map_comp]
    have hh := Functor.congr_hom
      (congrArg (fun F => F ⋙ Datum.localFunctor) he) f
    simp only [Functor.comp_map, Functor.const_obj_map] at hh
    erw [hh]
    simp only [eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    simp
    rfl

/-- Extraction retains the supplied local fiber, with only its base transported. -/
theorem fixedBaseObject_localFiber (z : Z) :
    HEq (fixedBaseObject A h E d he z).localFiber (E.obj z).localObject.fiber :=
  Fiber.localFiber_ofDatum _ _

/-- Exact base constancy gives a functor to the independent relative fiber. -/
def fixedBaseFunctor : Z ⥤ Fiber A h d where
  obj := fixedBaseObject A h E d he
  map := fixedBaseArrow A h E d he
  map_id z := by
    apply Fiber.Hom.ext
    change eqToHom _ ≫ E.map (𝟙 z) ≫ eqToHom _ = 𝟙 _
    rw [E.map_id]
    simp
  map_comp f g := by
    apply Fiber.Hom.ext
    change eqToHom _ ≫ E.map (f ≫ g) ≫ eqToHom _ =
      (eqToHom _ ≫ E.map f ≫ eqToHom _) ≫ (eqToHom _ ≫ E.map g ≫ eqToHom _)
    rw [E.map_comp]
    simp [Category.assoc]

/-- The fiber construction recovers the complete supplied total functor. -/
def fixedBaseComparison : fixedBaseFunctor A h E d he ⋙ Fiber.forget ≅ E :=
  NatIso.ofComponents (fun z => eqToIso (Fiber.datum_ofDatum (E.obj z) (Functor.congr_obj he z))) (by
    intro x y f
    change (eqToHom (Fiber.datum_ofDatum (E.obj x) (Functor.congr_obj he x)) ≫ E.map f ≫
      eqToHom (Fiber.datum_ofDatum (E.obj y) (Functor.congr_obj he y)).symm) ≫
      eqToHom (Fiber.datum_ofDatum (E.obj y) (Functor.congr_obj he y)) =
      eqToHom (Fiber.datum_ofDatum (E.obj x) (Functor.congr_obj he x)) ≫ E.map f
    simp [Category.assoc])

/-- Fiber inclusion followed by projection is constant, also after any functor. -/
theorem inclusion_forget_comp {C : Grpd.{u,u}} (F : C ⥤ Grpd.{u,u})
    {W : Type v} [Category.{u} W] (R : C ⥤ W) (c : C) :
    Grothendieck.ι (F ⋙ Grpd.forgetToCat) c ⋙
      (Grothendieck.forget (F ⋙ Grpd.forgetToCat) ⋙ R) =
      (Functor.const (F.obj c)).obj (R.obj c) := by
  apply CategoryTheory.Functor.ext
  · intro x y f
    change R.map (𝟙 c) = _
    simp
  · intro x
    rfl

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
