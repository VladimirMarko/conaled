import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberArrow

/-! Reconstructing a fiber also reconstructs precisely its vertical arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
variable {d : Datum D.toDiagram} {e f : Datum (A.total h).toDiagram}
variable (he : (A.projection h).functor.obj e = d)
variable (hf : (A.projection h).functor.obj f = d)

def ofDatumArrowEquiv :
    {p : e ⟶ f // (A.projection h).functor.map p ≫ eqToHom hf = eqToHom he} ≃
      (Fiber.ofDatum e he ⟶ Fiber.ofDatum f hf) where
  toFun p := ofDatumArrow he hf p.val p.property
  invFun p := ⟨eqToHom (Fiber.datum_ofDatum e he).symm ≫ p.matchingArrow ≫
    eqToHom (Fiber.datum_ofDatum f hf), by
      apply Datum.Hom.ext
      simp only [Functor.map_comp, eqToHom_map, Datum.comp_localArrow,
        Datum.eqToHom_localArrow]
      change (eqToHom _ ≫ p.matchingArrow.localArrow.base ≫ eqToHom _) ≫ eqToHom _ = _
      erw [p.vertical]
      change (eqToHom _ ≫ (𝟙 d.localObject) ≫ eqToHom _) ≫ eqToHom _ = eqToHom _
      simp only [Category.id_comp, eqToHom_trans]⟩
  left_inv p := by
    apply Subtype.ext
    simp only [ofDatumArrow, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, eqToHom_trans_assoc, Category.id_comp]
  right_inv p := by
    apply Fiber.Hom.ext
    simp only [ofDatumArrow, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, eqToHom_trans_assoc, Category.id_comp]

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
