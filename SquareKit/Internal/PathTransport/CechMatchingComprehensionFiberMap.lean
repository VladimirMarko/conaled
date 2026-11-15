import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor
import SquareKit.Internal.PathTransport.CechMatchingMapComposition

/-! Strict maps over a base diagram induce functors on the explicit matching fibers. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Fiber.forget_projection {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
    (d : Datum D.toDiagram) :
    Fiber.forget (A := A) (h := h) (d := d) ⋙ (A.projection h).functor =
      (Functor.const (Fiber A h d)).obj d := by
  refine CategoryTheory.Functor.ext (fun x => Fiber.projection_datum x) ?_
  intro x y f
  apply Datum.Hom.ext
  simp only [Datum.comp_localArrow, Datum.eqToHom_localArrow, Functor.const_obj_map,
    Datum.id_localArrow]
  change f.matchingArrow.localArrow.base = eqToHom _ ≫ (𝟙 d.localObject) ≫ eqToHom _
  rw [f.vertical]
  simp only [eqToHom_refl, Category.id_comp]

variable {D E : StrictDiagram.{u,u}} {A : FamilyData D} {B : FamilyData E}
variable {hA : A.Coherence} {hB : B.Coherence}
variable (S : StrictMap D E) (F : StrictMap (A.total hA) (B.total hB))
variable (sq : F.comp (B.projection hB) = (A.projection hA).comp S)

include sq in
theorem fiberMap_projection (d : Datum D.toDiagram) :
    (Fiber.forget (A := A) (h := hA) (d := d) ⋙ F.functor) ⋙ (B.projection hB).functor =
      (Functor.const (Fiber A hA d)).obj (S.functor.obj d) := by
  rw [Functor.assoc, ← StrictMap.functor_comp, sq, StrictMap.functor_comp,
    ← Functor.assoc, Fiber.forget_projection]
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro x y f
  simp only [Functor.comp_map, Functor.const_obj_map, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact S.functor.map_id d

def fiberMap (d : Datum D.toDiagram) : Fiber A hA d ⥤ Fiber B hB (S.functor.obj d) :=
  fixedBaseFunctor B hB (Fiber.forget ⋙ F.functor) (S.functor.obj d)
    (fiberMap_projection S F sq d)

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
